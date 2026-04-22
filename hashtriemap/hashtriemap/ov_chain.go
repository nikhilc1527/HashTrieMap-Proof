package hashtriemap

import (
	"sync"
	"sync/atomic"
)

type ovEntry struct {
	overflow atomic.Value // stores *ovEntry
	key      K
	value    V
}

func newOvEntry(key K, value V) *ovEntry {
	e := &ovEntry{key: key, value: value}
	e.overflow.Store((*ovEntry)(nil))
	return e
}

// OvChain is a concurrent map backed by a single overflow chain (linked list).
// It has the same key/value semantics as HashTrieMap but without hash-based
// indirection. Lookups are lock-free; mutations hold a single mutex.
//
// The zero OvChain is empty and ready to use.
// It must not be copied after first use.
type OvChain struct {
	once sync.Once
	mu   sync.Mutex
	head atomic.Value // stores *ovEntry
}

func (oc *OvChain) initOC() {
	oc.once.Do(func() {
		oc.head.Store((*ovEntry)(nil))
	})
}

// Load returns the value stored in the map for a key, or the zero value if no
// value is present. The ok result indicates whether value was found in the map.
func (oc *OvChain) Load(key K) (V, bool) {
	oc.initOC()
	e := oc.head.Load().(*ovEntry)
	for e != nil {
		if e.key == key {
			return e.value, true
		}
		e = e.overflow.Load().(*ovEntry)
	}
	return *new(V), false
}

// LoadOrStore returns the existing value for the key if present.
// Otherwise, it stores and returns the given value.
// The loaded result is true if the value was loaded, false if stored.
func (oc *OvChain) LoadOrStore(key K, value V) (result V, loaded bool) {
	oc.initOC()
	oc.mu.Lock()
	defer oc.mu.Unlock()

	head := oc.head.Load().(*ovEntry)
	for e := head; e != nil; e = e.overflow.Load().(*ovEntry) {
		if e.key == key {
			return e.value, true
		}
	}
	newE := newOvEntry(key, value)
	newE.overflow.Store(head)
	oc.head.Store(newE)
	return value, false
}

// Store sets the value for a key.
func (oc *OvChain) Store(key K, value V) {
	_, _ = oc.Swap(key, value)
}

// Swap sets the value for a key and returns the previous value if any.
// The loaded result reports whether the key was present.
func (oc *OvChain) Swap(key K, new V) (previous V, loaded bool) {
	oc.initOC()
	oc.mu.Lock()
	defer oc.mu.Unlock()

	head := oc.head.Load().(*ovEntry)
	if head != nil {
		if head.key == key {
			newE := newOvEntry(key, new)
			newE.overflow.Store(head.overflow.Load().(*ovEntry))
			oc.head.Store(newE)
			return head.value, true
		}
		i := &head.overflow
		for e := i.Load().(*ovEntry); e != nil; e = e.overflow.Load().(*ovEntry) {
			if e.key == key {
				newE := newOvEntry(key, new)
				newE.overflow.Store(e.overflow.Load().(*ovEntry))
				i.Store(newE)
				return e.value, true
			}
			i = &e.overflow
		}
	}
	newE := newOvEntry(key, new)
	newE.overflow.Store(head)
	oc.head.Store(newE)
	var zero V
	return zero, false
}

// CompareAndSwap swaps the old and new values for key
// if the value stored in the map is equal to old.
func (oc *OvChain) CompareAndSwap(key K, old, new V) bool {
	oc.initOC()
	oc.mu.Lock()
	defer oc.mu.Unlock()

	head := oc.head.Load().(*ovEntry)
	if head == nil {
		return false
	}
	if head.key == key && head.value == old {
		newE := newOvEntry(key, new)
		newE.overflow.Store(head.overflow.Load().(*ovEntry))
		oc.head.Store(newE)
		return true
	}
	i := &head.overflow
	for e := i.Load().(*ovEntry); e != nil; e = e.overflow.Load().(*ovEntry) {
		if e.key == key && e.value == old {
			newE := newOvEntry(key, new)
			newE.overflow.Store(e.overflow.Load().(*ovEntry))
			i.Store(newE)
			return true
		}
		i = &e.overflow
	}
	return false
}

// LoadAndDelete deletes the value for a key, returning the previous value if any.
// The loaded result reports whether the key was present.
func (oc *OvChain) LoadAndDelete(key K) (value V, loaded bool) {
	oc.initOC()
	oc.mu.Lock()
	defer oc.mu.Unlock()

	head := oc.head.Load().(*ovEntry)
	if head == nil {
		return *new(V), false
	}
	if head.key == key {
		oc.head.Store(head.overflow.Load().(*ovEntry))
		return head.value, true
	}
	i := &head.overflow
	for e := i.Load().(*ovEntry); e != nil; e = e.overflow.Load().(*ovEntry) {
		if e.key == key {
			i.Store(e.overflow.Load().(*ovEntry))
			return e.value, true
		}
		i = &e.overflow
	}
	return *new(V), false
}

// Delete deletes the value for a key.
func (oc *OvChain) Delete(key K) {
	_, _ = oc.LoadAndDelete(key)
}

// CompareAndDelete deletes the entry for key if its value is equal to old.
func (oc *OvChain) CompareAndDelete(key K, old V) bool {
	oc.initOC()
	oc.mu.Lock()
	defer oc.mu.Unlock()

	head := oc.head.Load().(*ovEntry)
	if head == nil {
		return false
	}
	if head.key == key && head.value == old {
		oc.head.Store(head.overflow.Load().(*ovEntry))
		return true
	}
	i := &head.overflow
	for e := i.Load().(*ovEntry); e != nil; e = e.overflow.Load().(*ovEntry) {
		if e.key == key && e.value == old {
			i.Store(e.overflow.Load().(*ovEntry))
			return true
		}
		i = &e.overflow
	}
	return false
}

// All returns an iterator over each key and value present in the map.
func (oc *OvChain) All() func(yield func(K, V) bool) {
	oc.initOC()
	return func(yield func(K, V) bool) {
		e := oc.head.Load().(*ovEntry)
		for e != nil {
			if !yield(e.key, e.value) {
				return
			}
			e = e.overflow.Load().(*ovEntry)
		}
	}
}

// Range calls f sequentially for each key and value present in the map.
// If f returns false, range stops the iteration.
func (oc *OvChain) Range(yield func(K, V) bool) {
	oc.initOC()
	e := oc.head.Load().(*ovEntry)
	for e != nil {
		if !yield(e.key, e.value) {
			return
		}
		e = e.overflow.Load().(*ovEntry)
	}
}

// Clear deletes all the entries, resulting in an empty OvChain.
func (oc *OvChain) Clear() {
	oc.initOC()
	oc.mu.Lock()
	defer oc.mu.Unlock()
	oc.head.Store((*ovEntry)(nil))
}
