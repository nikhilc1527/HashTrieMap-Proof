// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package hashtriemap

import (
	"sync"
	"sync/atomic"
)

type K = int
type V = int

// HashTrieMap is an implementation of a concurrent hash-trie. The implementation
// is designed around frequent loads, but offers decent performance for stores
// and deletes as well, especially if the map is larger. Its primary use-case is
// the unique package, but can be used elsewhere as well.
//
// The zero HashTrieMap is empty and ready to use.
// It must not be copied after first use.
type HashTrieMap struct {
	inited   atomic.Uint32
	initMu   sync.Mutex
	root     atomic.Value
	seed     uint64
}

func (ht *HashTrieMap) initHT() {
	if ht.inited.Load() == 0 {
		ht.initSlow()
	}
}

func (ht *HashTrieMap) initSlow() {
	ht.initMu.Lock()
	defer ht.initMu.Unlock()
	if ht.inited.Load() != 0 {
		// Someone got to it while we were waiting.
		return
	}

	// Set up root node, derive the hash function for the key, and the
	// equal function for the value, if any.
	ht.root.Store(newIndirectNode(nil))
	ht.seed = 0

	ht.inited.Store(1)
}

func hashInt(key K, seed uint64) uint64 {
	x := uint64(uint64(key)) ^ uint64(seed)
	x ^= x >> 33
	x *= 0xff51afd7ed558ccd
	x ^= x >> 33
	x *= 0xc4ceb9fe1a85ec53
	x ^= x >> 33
	return uint64(x)
}

// Load returns the value stored in the map for a key, or nil if no
// value is present.
// The ok result indicates whether value was found in the map.
func (ht *HashTrieMap) Load(key K) (value V, ok bool) {
	ht.initHT()
	hash := hashInt(key, ht.seed)

	i := ht.root.Load().(*indirect)
	hashShift := uint(hashBits)
	for hashShift != 0 {
		hashShift -= nChildrenLog2

		n := i.children[(hash>>hashShift)&nChildrenMask].Load().(*node)
		if n == nil {
			return *new(V), false
		}
		if n.isEntry {
			return n.entry().lookup(key)
		}
		i = n.indirect()
	}
	panic("internal/sync.HashTrieMap: ran out of hash bits while iterating")
}

// LoadOrStore returns the existing value for the key if present.
// Otherwise, it stores and returns the given value.
// The loaded result is true if the value was loaded, false if stored.
func (ht *HashTrieMap) LoadOrStore(key K, value V) (result V, loaded bool) {
	ht.initHT()
	hash := hashInt(key, ht.seed)
	var i *indirect
	var hashShift uint
	var slot *atomic.Value
	var n *node
	for {
		// Find the key or a candidate location for insertion.
		i = ht.root.Load().(*indirect)
		hashShift = uint(hashBits)
		haveInsertPoint := false
		for hashShift != 0 {
			hashShift -= nChildrenLog2

			slot = &i.children[(hash>>hashShift)&nChildrenMask]
			n = slot.Load().(*node)
			if n == nil {
				// We found a nil slot which is a candidate for insertion.
				haveInsertPoint = true
				break
			}
			if n.isEntry {
				// We found an existing entry, which is as far as we can go.
				// If it stays this way, we'll have to replace it with an
				// indirect node.
				if v, ok := n.entry().lookup(key); ok {
					return v, true
				}
				haveInsertPoint = true
				break
			}
			i = n.indirect()
		}
		if !haveInsertPoint {
			panic("internal/sync.HashTrieMap: ran out of hash bits while iterating")
		}

		// Grab the lock and double-check what we saw.
		i.mu.Lock()
		n = slot.Load().(*node)
		if (n == nil || n.isEntry) && !i.dead.Load() {
			// What we saw is still true, so we can continue with the insert.
			break
		}
		// We have to start over.
		i.mu.Unlock()
	}
	// N.B. This lock is held from when we broke out of the outer loop above.
	// We specifically break this out so that we can use defer here safely.
	// One option is to break this out into a new function instead, but
	// there's so much local iteration state used below that this turns out
	// to be cleaner.
	defer i.mu.Unlock()

	var oldEntry *entry
	if n != nil {
		oldEntry = n.entry()
		if v, ok := oldEntry.lookup(key); ok {
			// Easy case: by loading again, it turns out exactly what we wanted is here!
			return v, true
		}
	}
	newEntry := newEntryNode(key, value)
	if oldEntry == nil {
		// Easy case: create a new entry and store it.
		slot.Store(newEntry.node)
	} else {
		// We possibly need to expand the entry already there into one or more new nodes.
		//
		// Publish the node last, which will make both oldEntry and newEntry visible. We
		// don't want readers to be able to observe that oldEntry isn't in the tree.
		slot.Store(ht.expand(oldEntry, newEntry, hash, hashShift, i))
	}
	return value, false
}

// expand takes oldEntry and newEntry whose hashes conflict from bit 64 down to hashShift and
// produces a subtree of indirect nodes to hold the two new entries.
func (ht *HashTrieMap) expand(oldEntry, newEntry *entry, newHash uint64, hashShift uint, parent *indirect) *node {
	// Check for a hash collision.
	oldHash := hashInt(oldEntry.key, ht.seed)
	if oldHash == newHash {
		// Store the old entry in the new entry's overflow list, then store
		// the new entry.
		newEntry.overflow.Store(oldEntry)
		return newEntry.node
	}
	// We have to add an indirect node. Worse still, we may need to add more than one.
	newIndirect := newIndirectNode(parent)
	top := newIndirect
	for {
		if hashShift == 0 {
			panic("internal/sync.HashTrieMap: ran out of hash bits while inserting")
		}
		hashShift -= nChildrenLog2 // hashShift is for the level parent is at. We need to go deeper.
		oi := (oldHash >> hashShift) & nChildrenMask
		ni := (newHash >> hashShift) & nChildrenMask
		if oi != ni {
			newIndirect.children[oi].Store(oldEntry.node)
			newIndirect.children[ni].Store(newEntry.node)
			break
		}
		nextIndirect := newIndirectNode(newIndirect)
		newIndirect.children[oi].Store(nextIndirect.node)
		newIndirect = nextIndirect
	}
	return top.node
}

// Store sets the value for a key.
func (ht *HashTrieMap) Store(key K, old V) {
	_, _ = ht.Swap(key, old)
}

// Swap swaps the value for a key and returns the previous value if any.
// The loaded result reports whether the key was present.
func (ht *HashTrieMap) Swap(key K, new V) (previous V, loaded bool) {
	ht.initHT()
	hash := hashInt(key, ht.seed)
	var i *indirect
	var hashShift uint
	var slot *atomic.Value
	var n *node
	for {
		// Find the key or a candidate location for insertion.
		i = ht.root.Load().(*indirect)
		hashShift = uint(hashBits)
		haveInsertPoint := false
		for hashShift != 0 {
			hashShift -= nChildrenLog2

			slot = &i.children[(hash>>hashShift)&nChildrenMask]
			n = slot.Load().(*node)
			if n == nil || n.isEntry {
				// We found a nil slot which is a candidate for insertion,
				// or an existing entry that we'll replace.
				haveInsertPoint = true
				break
			}
			i = n.indirect()
		}
		if !haveInsertPoint {
			panic("internal/sync.HashTrieMap: ran out of hash bits while iterating")
		}

		// Grab the lock and double-check what we saw.
		i.mu.Lock()
		n = slot.Load().(*node)
		if (n == nil || n.isEntry) && !i.dead.Load() {
			// What we saw is still true, so we can continue with the insert.
			break
		}
		// We have to start over.
		i.mu.Unlock()
	}
	// N.B. This lock is held from when we broke out of the outer loop above.
	// We specifically break this out so that we can use defer here safely.
	// One option is to break this out into a new function instead, but
	// there's so much local iteration state used below that this turns out
	// to be cleaner.
	defer i.mu.Unlock()

	var zero V
	var oldEntry *entry
	if n != nil {
		// Swap if the keys compare.
		oldEntry = n.entry()
		newEntry, old, swapped := oldEntry.swap(key, new)
		if swapped {
			slot.Store(newEntry.node)
			return old, true
		}
	}
	// The keys didn't compare, so we're doing an insertion.
	newEntry := newEntryNode(key, new)
	if oldEntry == nil {
		// Easy case: create a new entry and store it.
		slot.Store(newEntry.node)
	} else {
		// We possibly need to expand the entry already there into one or more new nodes.
		//
		// Publish the node last, which will make both oldEntry and newEntry visible. We
		// don't want readers to be able to observe that oldEntry isn't in the tree.
		slot.Store(ht.expand(oldEntry, newEntry, hash, hashShift, i))
	}
	return zero, false
}

// CompareAndSwap swaps the old and new values for key
// if the value stored in the map is equal to old.
func (ht *HashTrieMap) CompareAndSwap(key K, old, new V) (swapped bool) {
	ht.initHT()
	hash := hashInt(key, ht.seed)

	// Find a node with the key and compare with it. n != nil if we found the node.
	i, _, slot, n := ht.find(key, hash, true, old)
	if i != nil {
		defer i.mu.Unlock()
	}
	if n == nil {
		return false
	}

	// Try to swap the entry.
	e, swapped := n.entry().compareAndSwap(key, old, new)
	if !swapped {
		// Nothing was actually swapped, which means the node is no longer there.
		return false
	}
	// Store the entry back because it changed.
	slot.Store(e.node)
	return true
}

// LoadAndDelete deletes the value for a key, returning the previous value if any.
// The loaded result reports whether the key was present.
func (ht *HashTrieMap) LoadAndDelete(key K) (value V, loaded bool) {
	ht.initHT()
	hash := hashInt(key, ht.seed)

	// Find a node with the key and compare with it. n != nil if we found the node.
	i, hashShift, slot, n := ht.find(key, hash, false, *new(V))
	if n == nil {
		if i != nil {
			i.mu.Unlock()
		}
		return *new(V), false
	}

	// Try to delete the entry.
	v, e, loaded := n.entry().loadAndDelete(key)
	if !loaded {
		// Nothing was actually deleted, which means the node is no longer there.
		i.mu.Unlock()
		return *new(V), false
	}
	if e != nil {
		// We didn't actually delete the whole entry, just one entry in the chain.
		// Nothing else to do, since the parent is definitely not empty.
		slot.Store(e.node)
		i.mu.Unlock()
		return v, true
	}
	// Delete the entry.
	slot.Store((*node)(nil))

	// Check if the node is now empty (and isn't the root), and delete it if able.
	for i.parent != nil && i.empty() {
		if hashShift == uint(hashBits) {
			panic("internal/sync.HashTrieMap: ran out of hash bits while iterating")
		}
		hashShift += nChildrenLog2

		// Delete the current node in the parent.
		parent := i.parent
		parent.mu.Lock()
		i.dead.Store(true)
		parent.children[(hash>>hashShift)&nChildrenMask].Store((*node)(nil))
		i.mu.Unlock()
		i = parent
	}
	i.mu.Unlock()
	return v, true
}

// Delete deletes the value for a key.
func (ht *HashTrieMap) Delete(key K) {
	_, _ = ht.LoadAndDelete(key)
}

// CompareAndDelete deletes the entry for key if its value is equal to old.
//
// If there is no current value for key in the map, CompareAndDelete returns false
// (even if the old value is the nil interface value).
func (ht *HashTrieMap) CompareAndDelete(key K, old V) (deleted bool) {
	ht.initHT()
	hash := hashInt(key, ht.seed)

	// Find a node with the key. n != nil if we found the node.
	i, hashShift, slot, n := ht.find(key, hash, true, old)
	if n == nil {
		if i != nil {
			i.mu.Unlock()
		}
		return false
	}

	// Try to delete the entry.
	e, deleted := n.entry().compareAndDelete(key, old)
	if !deleted {
		// Nothing was actually deleted, which means the node is no longer there.
		i.mu.Unlock()
		return false
	}
	if e != nil {
		// We didn't actually delete the whole entry, just one entry in the chain.
		// Nothing else to do, since the parent is definitely not empty.
		slot.Store(e.node)
		i.mu.Unlock()
		return true
	}
	// Delete the entry.
	slot.Store((*node)(nil))

	// Check if the node is now empty (and isn't the root), and delete it if able.
	for i.parent != nil && i.empty() {
		if hashShift == uint(hashBits) {
			panic("internal/sync.HashTrieMap: ran out of hash bits while iterating")
		}
		hashShift += nChildrenLog2

		// Delete the current node in the parent.
		parent := i.parent
		parent.mu.Lock()
		i.dead.Store(true)
		parent.children[(hash>>hashShift)&nChildrenMask].Store((*node)(nil))
		i.mu.Unlock()
		i = parent
	}
	i.mu.Unlock()
	return true
}

// find searches the tree for a node that contains key (hash must be the hash of key).
// If checkValue is true, then it will also enforce that the values are equal as well.
//
// Returns a non-nil node, which will always be an entry, if found.
//
// If i != nil then i.mu is locked, and it is the caller's responsibility to unlock it.
func (ht *HashTrieMap) find(key K, hash uint64, checkValue bool, value V) (i *indirect, hashShift uint, slot *atomic.Value, n *node) {
	for {
		// Find the key or return if it's not there.
		i = ht.root.Load().(*indirect)
		hashShift = uint(hashBits)
		found := false
		for hashShift != 0 {
			hashShift -= nChildrenLog2

			slot = &i.children[(hash>>hashShift)&nChildrenMask]
			n = slot.Load().(*node)
			if n == nil {
				// Nothing to compare with. Give up.
				i = nil
				return
			}
			if n.isEntry {
				// We found an entry. Check if it matches.
				if _, ok := n.entry().lookupWithValue(key, value, checkValue); !ok {
					// No match, comparison failed.
					i = nil
					n = nil
					return
				}
				// We've got a match. Prepare to perform an operation on the key.
				found = true
				break
			}
			i = n.indirect()
		}
		if !found {
			panic("internal/sync.HashTrieMap: ran out of hash bits while iterating")
		}

		// Grab the lock and double-check what we saw.
		i.mu.Lock()
		n = slot.Load().(*node)
		if !i.dead.Load() && (n == nil || n.isEntry) {
			// Either we've got a valid node or the node is now nil under the lock.
			// In either case, we're done here.
			return
		}
		// We have to start over.
		i.mu.Unlock()
	}
}

// All returns an iterator over each key and value present in the map.
//
// The iterator does not necessarily correspond to any consistent snapshot of the
// HashTrieMap's contents: no key will be visited more than once, but if the value
// for any key is stored or deleted concurrently (including by yield), the iterator
// may reflect any mapping for that key from any point during iteration. The iterator
// does not block other methods on the receiver; even yield itself may call any
// method on the HashTrieMap.
func (ht *HashTrieMap) All() func(yield func(K, V) bool) {
	ht.initHT()
	return func(yield func(key K, value V) bool) {
		ht.iter(ht.root.Load().(*indirect), yield)
	}
}

// Range calls f sequentially for each key and value present in the map.
// If f returns false, range stops the iteration.
//
// This exists for compatibility with sync.Map; All should be preferred.
// It provides the same guarantees as sync.Map, and All.
func (ht *HashTrieMap) Range(yield func(K, V) bool) {
	ht.initHT()
	ht.iter(ht.root.Load().(*indirect), yield)
}

func (ht *HashTrieMap) iter(i *indirect, yield func(key K, value V) bool) bool {
	for j := range i.children[:] {
		n := i.children[j].Load().(*node)
		if n == nil {
			continue
		}
		if !n.isEntry {
			if !ht.iter(n.indirect(), yield) {
				return false
			}
			continue
		}
		e := n.entry()
		for e != nil {
			if !yield(e.key, e.value) {
				return false
			}
			e = e.overflow.Load().(*entry)
		}
	}
	return true
}

// Clear deletes all the entries, resulting in an empty HashTrieMap.
func (ht *HashTrieMap) Clear() {
	ht.initHT()

	// It's sufficient to just drop the root on the floor, but the root
	// must always be non-nil.
	ht.root.Store(newIndirectNode(nil))
}

const (
	// 16 children. This seems to be the sweet spot for
	// load performance: any smaller and we lose out on
	// 50% or more in CPU performance. Any larger and the
	// returns are minuscule (~1% improvement for 32 children).
	nChildrenLog2 = 4
	nChildren     = 1 << nChildrenLog2
	nChildrenMask = nChildren - 1
	hashBits      = 64
)

// indirect is an internal node in the hash-trie.
type indirect struct {
	node     *node
	dead     atomic.Bool
	mu       sync.Mutex // Protects mutation to children and any children that are entry nodes.
	parent   *indirect
	children [nChildren]atomic.Value
}

func newIndirectNode(parent *indirect) *indirect {
	i := &indirect{parent: parent}
	for idx := range i.children[:] {
		i.children[idx].Store((*node)(nil))
	}
	i.node = &node{isEntry: false, ind: i}
	return i
}

func (i *indirect) empty() bool {
	nc := 0
	for j := range i.children[:] {
		if i.children[j].Load().(*node) != nil {
			nc++
		}
	}
	return nc == 0
}

// entry is a leaf node in the hash-trie.
type entry struct {
	node  *node
	overflow atomic.Value // Overflow for hash collisions.
	key      K
	value    V
}

func newEntryNode(key K, value V) *entry {
	e := &entry{
		key:      key,
		value:    value,
	}
	e.overflow.Store((*entry)(nil))
	e.node = &node{isEntry: true, ent: e}
	return e
}

func (e *entry) lookup(key K) (V, bool) {
	for e != nil {
		if e.key == key {
			return e.value, true
		}
		e = e.overflow.Load().(*entry)
	}
	return *new(V), false
}

func (e *entry) lookupWithValue(key K, value V, checkValue bool) (V, bool) {
	for e != nil {
		if e.key == key && (!checkValue || e.value == value) {
			return e.value, true
		}
		e = e.overflow.Load().(*entry)
	}
	return *new(V), false
}

// swap replaces an entry in the overflow chain if keys compare equal. Returns the new entry chain,
// the old value, and whether or not anything was swapped.
//
// swap must be called under the mutex of the indirect node which e is a child of.
func (head *entry) swap(key K, new V) (*entry, V, bool) {
	if head.key == key {
		// Return the new head of the list.
		e := newEntryNode(key, new)
		if chain := head.overflow.Load().(*entry); chain != nil {
			e.overflow.Store(chain)
		}
		return e, head.value, true
	}
	i := &head.overflow
	e := i.Load().(*entry)
	for e != nil {
		if e.key == key {
			eNew := newEntryNode(key, new)
			eNew.overflow.Store(e.overflow.Load().(*entry))
			i.Store(eNew)
			return head, e.value, true
		}
		i = &e.overflow
		e = e.overflow.Load().(*entry)
	}
	var zero V
	return head, zero, false
}

// compareAndSwap replaces an entry in the overflow chain if both the key and value compare
// equal. Returns the new entry chain and whether or not anything was swapped.
//
// compareAndSwap must be called under the mutex of the indirect node which e is a child of.
func (head *entry) compareAndSwap(key K, old, new V) (*entry, bool) {
	if head.key == key && head.value == old {
		// Return the new head of the list.
		e := newEntryNode(key, new)
		if chain := head.overflow.Load().(*entry); chain != nil {
			e.overflow.Store(chain)
		}
		return e, true
	}
	i := &head.overflow
	e := i.Load().(*entry)
	for e != nil {
		if e.key == key && e.value == old {
			eNew := newEntryNode(key, new)
			eNew.overflow.Store(e.overflow.Load().(*entry))
			i.Store(eNew)
			return head, true
		}
		i = &e.overflow
		e = e.overflow.Load().(*entry)
	}
	return head, false
}

// loadAndDelete deletes an entry in the overflow chain by key. Returns the value for the key, the new
// entry chain and whether or not anything was loaded (and deleted).
//
// loadAndDelete must be called under the mutex of the indirect node which e is a child of.
func (head *entry) loadAndDelete(key K) (V, *entry, bool) {
	if head.key == key {
		// Drop the head of the list.
		return head.value, head.overflow.Load().(*entry), true
	}
	i := &head.overflow
	e := i.Load().(*entry)
	for e != nil {
		if e.key == key {
			i.Store(e.overflow.Load().(*entry))
			return e.value, head, true
		}
		i = &e.overflow
		e = e.overflow.Load().(*entry)
	}
	return *new(V), head, false
}

// compareAndDelete deletes an entry in the overflow chain if both the key and value compare
// equal. Returns the new entry chain and whether or not anything was deleted.
//
// compareAndDelete must be called under the mutex of the indirect node which e is a child of.
func (head *entry) compareAndDelete(key K, value V) (*entry, bool) {
	if head.key == key && head.value == value {
		// Drop the head of the list.
		return head.overflow.Load().(*entry), true
	}
	i := &head.overflow
	e := i.Load().(*entry)
	for e != nil {
		if e.key == key && e.value == value {
			i.Store(e.overflow.Load().(*entry))
			return head, true
		}
		i = &e.overflow
		e = e.overflow.Load().(*entry)
	}
	return head, false
}

// node is the header for a node. It's polymorphic and
// is actually either an entry or an indirect.
type node struct {
	isEntry bool
	ent     *entry
	ind     *indirect
}

func (n *node) entry() *entry {
	if !n.isEntry {
		panic("called entry on non-entry node")
	}
	return n.ent
}

func (n *node) indirect() *indirect {
	if n.isEntry {
		panic("called indirect on entry node")
	}
	return n.ind
}
