// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package hashtriemap

import (
	"math"
	"runtime"
	"sync"
	"testing"
)

func TestHashTrieMapBasic(t *testing.T) {
	var m HashTrieMap

	t.Run("LoadEmpty", func(t *testing.T) {
		for _, k := range testData {
			expectMissing(t, k, 0)(m.Load(k))
		}
	})
	t.Run("LoadOrStore", func(t *testing.T) {
		for i, k := range testData {
			expectMissing(t, k, 0)(m.Load(k))
			expectStored(t, k, i)(m.LoadOrStore(k, i))
			expectPresent(t, k, i)(m.Load(k))
			expectLoaded(t, k, i)(m.LoadOrStore(k, 0))
		}
	})
	t.Run("All", func(t *testing.T) {
		var m HashTrieMap
		testAll(t, &m, testDataMap(testData), func(_ int, _ int) bool { return true })
	})
	t.Run("Clear", func(t *testing.T) {
		var m HashTrieMap
		for i, k := range testData {
			expectStored(t, k, i)(m.LoadOrStore(k, i))
		}
		m.Clear()
		for _, k := range testData {
			expectMissing(t, k, 0)(m.Load(k))
		}
	})
	t.Run("CompareAndDelete", func(t *testing.T) {
		var m HashTrieMap
		for i, k := range testData {
			expectStored(t, k, i)(m.LoadOrStore(k, i))
		}
		for i, k := range testData {
			expectNotDeleted(t, k, math.MaxInt)(m.CompareAndDelete(k, math.MaxInt))
			expectDeleted(t, k, i)(m.CompareAndDelete(k, i))
			expectNotDeleted(t, k, i)(m.CompareAndDelete(k, i))
			expectMissing(t, k, 0)(m.Load(k))
		}
	})
	t.Run("CompareAndSwap", func(t *testing.T) {
		var m HashTrieMap
		for i, k := range testData {
			expectStored(t, k, i)(m.LoadOrStore(k, i))
		}
		for i, k := range testData {
			expectNotSwapped(t, k, math.MaxInt, i+1)(m.CompareAndSwap(k, math.MaxInt, i+1))
			expectSwapped(t, k, i, i+1)(m.CompareAndSwap(k, i, i+1))
			expectPresent(t, k, i+1)(m.Load(k))
		}
	})
	t.Run("LoadAndDelete", func(t *testing.T) {
		var m HashTrieMap
		for i, k := range testData {
			expectStored(t, k, i)(m.LoadOrStore(k, i))
		}
		for i, k := range testData {
			expectLoadedFromDelete(t, k, i)(m.LoadAndDelete(k))
			expectMissing(t, k, 0)(m.Load(k))
		}
	})
}

func TestHashTrieMapConcurrent(t *testing.T) {
	t.Run("Clear", func(t *testing.T) {
		var m HashTrieMap
		for i, k := range testData {
			expectStored(t, k, i)(m.LoadOrStore(k, i))
		}

		gmp := runtime.GOMAXPROCS(-1)
		var wg sync.WaitGroup
		for i := range gmp {
			wg.Add(1)
			go func(id int) {
				defer wg.Done()
				for _, k := range testData {
					expectNotDeleted(t, k, math.MaxInt)(m.CompareAndDelete(k, math.MaxInt))
					m.CompareAndSwap(k, id, id+1)
				}
			}(i)
		}
		runtime.Gosched()
		m.Clear()
		wg.Wait()

		for _, k := range testData {
			expectMissing(t, k, 0)(m.Load(k))
		}
	})

	t.Run("SharedKeys", func(t *testing.T) {
		var m HashTrieMap
		for i, k := range testData {
			expectStored(t, k, i)(m.LoadOrStore(k, i))
		}
		gmp := runtime.GOMAXPROCS(-1)
		var wg sync.WaitGroup
		for i := range gmp {
			wg.Add(1)
			go func(id int) {
				defer wg.Done()
				for i, k := range testData {
					m.CompareAndSwap(k, i, i+1)
					expectPresent(t, k, i+1)(m.Load(k))
				}
			}(i)
		}
		wg.Wait()
	})

	t.Run("UnsharedKeys", func(t *testing.T) {
		var m HashTrieMap
		gmp := runtime.GOMAXPROCS(-1)
		var wg sync.WaitGroup
		for i := range gmp {
			wg.Add(1)
			go func(id int) {
				defer wg.Done()
				base := id * 1000
				for _, k := range testData {
					key := base + k
					expectMissing(t, key, 0)(m.Load(key))
					expectStored(t, key, id)(m.LoadOrStore(key, id))
					expectPresent(t, key, id)(m.Load(key))
					expectLoaded(t, key, id)(m.LoadOrStore(key, 0))
					expectSwapped(t, key, id, id+1)(m.CompareAndSwap(key, id, id+1))
					expectPresent(t, key, id+1)(m.Load(key))
					expectDeleted(t, key, id+1)(m.CompareAndDelete(key, id+1))
					expectMissing(t, key, 0)(m.Load(key))
				}
			}(i)
		}
		wg.Wait()
	})
}

func testAll(t *testing.T, m *HashTrieMap, testData map[int]int, yield func(int, int) bool) {
	for k, v := range testData {
		expectStored(t, k, v)(m.LoadOrStore(k, v))
	}
	visited := make(map[int]int)
	m.All()(func(key int, got int) bool {
		want, ok := testData[key]
		if !ok {
			t.Errorf("unexpected key %v in map", key)
			return false
		}
		if got != want {
			t.Errorf("expected key %v to have value %v, got %v", key, want, got)
			return false
		}
		visited[key]++
		return yield(key, got)
	})
	for key, n := range visited {
		if n > 1 {
			t.Errorf("visited key %v more than once", key)
		}
	}
}

func expectPresent(t *testing.T, key, want int) func(got int, ok bool) {
	t.Helper()
	return func(got int, ok bool) {
		t.Helper()
		if !ok {
			t.Errorf("expected key %v to be present in map", key)
		}
		if ok && got != want {
			t.Errorf("expected key %v to have value %v, got %v", key, want, got)
		}
	}
}

func expectMissing(t *testing.T, key, want int) func(got int, ok bool) {
	t.Helper()
	if want != 0 {
		panic("expectMissing must always have a zero value variable")
	}
	return func(got int, ok bool) {
		t.Helper()
		if ok {
			t.Errorf("expected key %v to be missing from map, got value %v", key, got)
		}
		if !ok && got != want {
			t.Errorf("expected missing key %v to be paired with zero value; got %v", key, got)
		}
	}
}

func expectLoaded(t *testing.T, key, want int) func(got int, loaded bool) {
	t.Helper()
	return func(got int, loaded bool) {
		t.Helper()
		if !loaded {
			t.Errorf("expected key %v to have been loaded, not stored", key)
		}
		if got != want {
			t.Errorf("expected key %v to have value %v, got %v", key, want, got)
		}
	}
}

func expectStored(t *testing.T, key, want int) func(got int, loaded bool) {
	t.Helper()
	return func(got int, loaded bool) {
		t.Helper()
		if loaded {
			t.Errorf("expected inserted key %v to have been stored, not loaded", key)
		}
		if got != want {
			t.Errorf("expected inserted key %v to have value %v, got %v", key, want, got)
		}
	}
}

func expectDeleted(t *testing.T, key, old int) func(deleted bool) {
	t.Helper()
	return func(deleted bool) {
		t.Helper()
		if !deleted {
			t.Errorf("expected key %v with value %v to be in map and deleted", key, old)
		}
	}
}

func expectNotDeleted(t *testing.T, key, old int) func(deleted bool) {
	t.Helper()
	return func(deleted bool) {
		t.Helper()
		if deleted {
			t.Errorf("expected key %v with value %v to not be in map and thus not deleted", key, old)
		}
	}
}

func expectSwapped(t *testing.T, key, old, new int) func(swapped bool) {
	t.Helper()
	return func(swapped bool) {
		t.Helper()
		if !swapped {
			t.Errorf("expected key %v with value %v to be in map and swapped for %v", key, old, new)
		}
	}
}

func expectNotSwapped(t *testing.T, key, old, new int) func(swapped bool) {
	t.Helper()
	return func(swapped bool) {
		t.Helper()
		if swapped {
			t.Errorf("expected key %v with value %v to not be in map or not swapped for %v", key, old, new)
		}
	}
}

func expectLoadedFromDelete(t *testing.T, key, want int) func(got int, loaded bool) {
	t.Helper()
	return func(got int, loaded bool) {
		t.Helper()
		if !loaded {
			t.Errorf("expected key %v to be in map to be deleted", key)
		} else if want != got {
			t.Errorf("key %v was deleted with value %v, but expected it to have value %v", key, got, want)
		}
	}
}

func testDataMap(data []int) map[int]int {
	m := make(map[int]int)
	for i, k := range data {
		m[k] = i
	}
	return m
}

var testData = func() []int {
	out := make([]int, 128)
	for i := range out {
		out[i] = i
	}
	return out
}()
