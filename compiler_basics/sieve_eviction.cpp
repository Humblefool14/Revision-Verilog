#include <iostream>
#include <unordered_map>
#include <string>

class Node {
public:
    std::string value;
    bool visited;
    Node* prev;
    Node* next;

    Node(const std::string& val) : value(val), visited(false), prev(nullptr), next(nullptr) {}
};

class SieveCache {
private:
    int capacity;
    std::unordered_map<std::string, Node*> cache;
    Node* head;
    Node* tail;
    Node* hand;
    int size;

    void addToHead(Node* node) {
        node->next = head;
        node->prev = nullptr;
        if (head) {
            head->prev = node;
        }
        //  In SIEVE (and many other caching algorithms),
        // newly added items are considered the most recently used 
        // and are placed at the head of the list.
        head = node;
        if (!tail) {
            tail = node;
        }
    }

    void removeNode(Node* node) {
        if (node->prev) {
            node->prev->next = node->next;
        } else {
            head = node->next;
        }
        if (node->next) {
            node->next->prev = node->prev;
        } else {
            tail = node->prev;
        }
    }

    void evict() {
        Node* obj = hand ? hand : tail;
        // During eviction, 
        //the algorithm scans from the "hand" towards the head of the list, 
        //marking items as not visited until it finds an item that's already not visited. This item is then evicted.
        while (obj && obj->visited) {
            obj->visited = false;
            obj = obj->prev ? obj->prev : tail;
        }
        hand = obj->prev ? obj->prev : nullptr;
        cache.erase(obj->value);// remove the value. 
        removeNode(obj);
        // Delete the node. 
        // First delete the value to remove the dangling pointer 
        // then the object connection. 
        delete obj;
        size--;
    }

public:
    SieveCache(int cap) : capacity(cap), head(nullptr), tail(nullptr), hand(nullptr), size(0) {}

    ~SieveCache() {
        Node* current = head;
        while (current) {
            Node* next = current->next;
            delete current;
            current = next;
        }
    }

    void access(const std::string& x) {
        if (cache.find(x) != cache.end()) {  // Cache Hit
            Node* node = cache[x];
            node->visited = true;
        } else {  // Cache Miss
            if (size == capacity) {  // Cache Full
                evict();  // Eviction
            }
            Node* newNode = new Node(x);
            addToHead(newNode);
            cache[x] = newNode;
            size++;
            newNode->visited = false;  // Insertion
            //  In the SIEVE algorithm, 
            // newly inserted items are initially marked as not visited. 
        }
    }

    void showCache() {
        Node* current = head;
        while (current) {
            std::cout << current->value << " (Visited: " << (current->visited ? "true" : "false") << ")";
            if (current->next) {
                std::cout << " -> ";
            } else {
                std::cout << std::endl;
            }
            current = current->next;
        }
    }
};

int main() {
    SieveCache cache(3);
    cache.access("A");
    cache.showCache();
    cache.access("B");
    cache.showCache();
    cache.access("C");
    cache.showCache();
    cache.access("D");
    cache.showCache();
    cache.access("D");
    cache.showCache();
    cache.access("B");
    cache.showCache();
    cache.access("A");
    cache.showCache();
    cache.access("B");
    cache.showCache();
    return 0;
}

// Three modes:
// 1. Cache hit --> change the visited mode to true, 
// 2. cache full ---> evict the node which is least visited. 
// 3. cache not full but new node value is reached ---> add the node to list. 