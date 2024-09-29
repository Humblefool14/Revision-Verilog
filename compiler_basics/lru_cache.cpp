#include <unordered_map>
#include <list>
#include <iostream>

template<typename Key, typename Value>
class LRUCache {
private:
    int capacity;
    std::list<std::pair<Key, Value>> items;
    std::unordered_map<Key, typename std::list<std::pair<Key, Value>>::iterator> cache;

public:
    LRUCache(int size) : capacity(size) {}

    void put(const Key& key, const Value& value) {
        auto it = cache.find(key);
        if (it != cache.end()) {
            // Key exists, update value and move to front
            items.erase(it->second);
        } else if (cache.size() >= capacity) {
            // Cache is full, remove least recently used item
            auto last = items.back();
            cache.erase(last.first);
            items.pop_back();
        }
        items.push_front({key, value});
        cache[key] = items.begin();
    }

    Value get(const Key& key) {
        auto it = cache.find(key);
        if (it == cache.end()) {
            throw std::runtime_error("Key not found");
        }
        // Move accessed item to front
        items.splice(items.begin(), items, it->second);
        return it->second->second;
    }

    bool contains(const Key& key) const {
        return cache.find(key) != cache.end();
    }

    int size() const {
        return cache.size();
    }

    void print() const {
        for (const auto& item : items) {
            std::cout << item.first << ": " << item.second << std::endl;
        }
    }
};

// Example usage
int main() {
    LRUCache<int, std::string> cache(3);
    
    cache.put(1, "one");
    cache.put(2, "two");
    cache.put(3, "three");
    cache.print();
    
    std::cout << "Get 2: " << cache.get(2) << std::endl;
    
    cache.put(4, "four");
    cache.print();
    
    return 0;
}