// SOURCE: https://github.com/Ten0/updatable_priority_queue/blob/master/updatable_priority_queue.h

#include <utility>
#include <vector>

namespace updatable_priority_queue {
	template <typename Key, typename Priority>
		struct priority_queue_node {
			Priority priority;
			Key key;
			priority_queue_node(const Key& key, const Priority& priority) : priority(priority), key(key) {}
			friend bool operator<(const priority_queue_node& pqn1, const priority_queue_node& pqn2) {
				return pqn1.priority > pqn2.priority;
			}
			friend bool operator>(const priority_queue_node& pqn1, const priority_queue_node& pqn2) {
				return pqn1.priority < pqn2.priority;
			}
		};

	/** Key has to be an uint value (convertible to size_t)
	 * This is a max heap (max is on top), to match stl's pQ */
	template <typename Key, typename Priority>
		class priority_queue {
			protected:
				std::vector<size_t> id_to_heappos;
				std::vector<priority_queue_node<Key,Priority>> heap;
				std::size_t max_size = 4; // std::numeric_limits<std::size_t>::max(); // Create a variable max_size that defaults to the largest size_t value possible

			public:
				// priority_queue() {}
				priority_queue(std::size_t max_size = std::numeric_limits<std::size_t>::max()): max_size(max_size) {}

				// Returns a const reference to the internal heap storage
				const std::vector<priority_queue_node<Key, Priority>>& get_heap() const {
					return heap;
				}

				bool empty()       const { return heap.empty(); }
				std::size_t size() const { return heap.size(); }

				/** first is priority, second is key */
				const priority_queue_node<Key,Priority>& top() const { return heap.front(); }

				void pop(bool remember_key=false) {
					if(size() == 0) return;
					id_to_heappos[heap.front().key] = -1-remember_key;
					if(size() > 1) {
						*heap.begin() = std::move(*(heap.end()-1));
						id_to_heappos[heap.front().key] = 0;
					}
					heap.pop_back();
					sift_down(0);
				}

				priority_queue_node<Key,Priority> pop_value(bool remember_key=true) {
					if(size() == 0) return priority_queue_node<Key, Priority>(-1, Priority());
					priority_queue_node<Key,Priority> ret = std::move(*heap.begin());
					id_to_heappos[ret.key] = -1-remember_key;
					if(size() > 1) {
						*heap.begin() = std::move(*(heap.end()-1));
						id_to_heappos[heap.front().key] = 0;
					}
					heap.pop_back();
					sift_down(0);
					return ret;
				}

				/** Sets the priority for the given key. If not present, it will be added, otherwise it will be updated
				 *  Returns true if the priority was changed.
				 * */
				bool set(const Key& key, const Priority& priority, bool only_if_higher=false) {
					if(key < id_to_heappos.size() && id_to_heappos[key] < ((size_t)-2)) // This key is already in the pQ
						return update(key, priority, only_if_higher);
					else
						return push(key, priority, only_if_higher);
				}

				std::pair<bool,Priority> get_priority(const Key& key) {
					if(key < id_to_heappos.size()) {
						size_t pos = id_to_heappos[key];
						if(pos < ((size_t)-2)) {
							return {true, heap[pos].priority};
						}
					}
					return {false, 0};
				}

				/** Returns true if the key was not inside and was added, otherwise does nothing and returns false
				 *  If the key was remembered and only_if_unknown is true, does nothing and returns false
				 * */
				bool push(const Key& key, const Priority& priority, bool only_if_unknown = false) {
    				extend_ids(key);
					if (id_to_heappos[key] < ((size_t)-2)) return false; // already inside
					if (only_if_unknown && id_to_heappos[key] == ((size_t)-2)) return false; // was evicted and only_if_unknown prevents re-adding

					if (heap.size() < max_size) {
						// We have room: just add new element
						size_t n = heap.size();
						id_to_heappos[key] = n;
						heap.emplace_back(key, priority);
						sift_up(n);
						return true;
					} else {
						// Heap full: heap[0] is the smallest priority in the top-k (min-heap)
						if (priority <= heap[0].priority) {
							// New element priority too small or equal, discard it
							return false;
						}
						// Evict smallest element at heap[0]
						Key evicted_key = heap[0].key;
						id_to_heappos[evicted_key] = -2; // Mark evicted

						heap[0] = priority_queue_node<Key, Priority>(key, priority);
						id_to_heappos[key] = 0;
						sift_down(0); // restore min-heap property
						return true;
					}
				}



				/** Returns true if the key was already inside and was updated, otherwise does nothing and returns false */
				bool update(const Key& key, const Priority& new_priority, bool only_if_higher=false) {
					if(key >= id_to_heappos.size()) return false;
					size_t heappos = id_to_heappos[key];
					if(heappos >= ((size_t)-2)) return false;
					Priority& priority = heap[heappos].priority;
					if(new_priority > priority) {
						priority = new_priority;
						sift_up(heappos);
						return true;
					}
					else if(!only_if_higher && new_priority < priority) {
						priority = new_priority;
						sift_down(heappos);
						return true;
					}
					return false;
				}

				void clear() {
					heap.clear();
					id_to_heappos.clear();
				}


			private:
				void extend_ids(Key k) {
					size_t new_size = k+1;
					if(id_to_heappos.size() < new_size)
						id_to_heappos.resize(new_size, -1);
				}

				void sift_down(size_t heappos) {
					size_t len = heap.size();
					size_t child = heappos*2+1;
					if(len < 2 || child >= len) return;
					if(child+1 < len && heap[child+1] > heap[child]) ++child; // Check whether second child is higher
					if(!(heap[child] > heap[heappos])) return; // Already in heap order

					priority_queue_node<Key,Priority> val = std::move(heap[heappos]);
					do {
						heap[heappos] = std::move(heap[child]);
						id_to_heappos[heap[heappos].key] = heappos;
						heappos = child;
						child = 2*child+1;
						if(child >= len) break;
						if(child+1 < len && heap[child+1] > heap[child]) ++child;
					} while(heap[child] > val);
					heap[heappos] = std::move(val);
					id_to_heappos[heap[heappos].key] = heappos;
				}

				void sift_up(size_t heappos) {
					size_t len = heap.size();
					if(len < 2 || heappos <= 0) return;
					size_t parent = (heappos-1)/2;
					if(!(heap[heappos] > heap[parent])) return;
					priority_queue_node<Key, Priority> val = std::move(heap[heappos]);
					do {
						heap[heappos] = std::move(heap[parent]);
						id_to_heappos[heap[heappos].key] = heappos;
						heappos = parent;
						if(heappos <= 0) break;
						parent = (parent-1)/2;
					} while(val > heap[parent]);
					heap[heappos] = std::move(val);
					id_to_heappos[heap[heappos].key] = heappos;
				}
		};
}