#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <string>

// Class to represent a vertex/node in the control flow graph
class Vertex {
public:
    int id;
    std::set<int> successors;     // Set of successor vertices
    std::set<std::string> use;    // Variables used in this vertex
    std::set<std::string> def;    // Variables defined in this vertex
    std::set<std::string> in;     // Live variables at entry
    std::set<std::string> out;    // Live variables at exit
    std::set<std::string> in_old; // Previous iteration's in set
    std::set<std::string> out_old;// Previous iteration's out set

    Vertex(int _id) : id(_id) {}

    void print() const {
        std::cout << "Vertex " << id << ":\n";
        printSet("USE", use);
        printSet("DEF", def);
        printSet("IN", in);
        printSet("OUT", out);
        std::cout << "Successors: ";
        for(int succ : successors) {
            std::cout << succ << " ";
        }
        std::cout << "\n\n";
    }

private:
    void printSet(const std::string& name, const std::set<std::string>& s) const {
        std::cout << name << " = {";
        bool first = true;
        for(const auto& elem : s) {
            if(!first) std::cout << ", ";
            std::cout << elem;
            first = false;
        }
        std::cout << "}\n";
    }
};

class LivenessAnalyzer {
private:
    std::vector<Vertex> vertices;

    // Compute set difference (s1 - s2)
    std::set<std::string> setDifference(const std::set<std::string>& s1, 
                                      const std::set<std::string>& s2) {
        std::set<std::string> result;
        for(const auto& elem : s1) {
            if(s2.find(elem) == s2.end()) {
                result.insert(elem);
            }
        }
        return result;
    }

    // Compute set union (s1 ∪ s2)
    std::set<std::string> setUnion(const std::set<std::string>& s1, 
                                  const std::set<std::string>& s2) {
        std::set<std::string> result = s1;
        result.insert(s2.begin(), s2.end());
        return result;
    }

public:
    void addVertex(const Vertex& v) {
        vertices.push_back(v);
    }

    void analyze() {
        // Initialize all in[] and out[] sets to empty
        for(auto& v : vertices) {
            v.in.clear();
            v.out.clear();
        }

        while(true) {
            bool changed = false;

            // For each vertex
            for(auto& v : vertices) {
                // Save old values
                v.in_old = v.in;
                v.out_old = v.out;

                // Compute new out[v] = ∪ in[w] for all successors w
                v.out.clear();
                for(int succId : v.successors) {
                    const auto& succIn = vertices[succId].in;
                    v.out = setUnion(v.out, succIn);
                }

                // Compute new in[v] = use[v] ∪ (out[v] - def[v])
                std::set<std::string> outMinusDef = setDifference(v.out, v.def);
                v.in = setUnion(v.use, outMinusDef);

                // Check if anything changed
                if(v.in != v.in_old || v.out != v.out_old) {
                    changed = true;
                }
            }

            // If nothing changed, we've reached a fixed point
            if(!changed) break;
        }
    }

    void printResults() {
        std::cout << "Liveness Analysis Results:\n";
        std::cout << "=========================\n";
        for(const auto& v : vertices) {
            v.print();
        }
    }
};

int main() {
    LivenessAnalyzer analyzer;

    // Example: Create a simple control flow graph
    // x = 1
    // y = x + 2
    // if(y > 0)
    //   z = y
    // else
    //   z = x
    // print z

    Vertex v0(0);  // x = 1
    v0.def = {"x"};
    v0.successors = {1};

    Vertex v1(1);  // y = x + 2
    v1.use = {"x"};
    v1.def = {"y"};
    v1.successors = {2, 3};

    Vertex v2(2);  // z = y
    v2.use = {"y"};
    v2.def = {"z"};
    v2.successors = {4};

    Vertex v3(3);  // z = x
    v3.use = {"x"};
    v3.def = {"z"};
    v3.successors = {4};

    Vertex v4(4);  // print z
    v4.use = {"z"};

    // Add vertices to analyzer
    analyzer.addVertex(v0);
    analyzer.addVertex(v1);
    analyzer.addVertex(v2);
    analyzer.addVertex(v3);
    analyzer.addVertex(v4);

    // Run analysis
    analyzer.analyze();

    // Print results
    analyzer.printResults();

    return 0;
}