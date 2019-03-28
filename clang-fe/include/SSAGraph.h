#ifndef SSA_TRANSFORM_SSAGRAPH_H
#define SSA_TRANSFORM_SSAGRAPH_H

#include <vector>
#include <utility>
#include <future>
#include <string>
#include <set>
#include <list>
#include <llvm/Support/raw_ostream.h>
#include <map>

namespace ssa_transform {

    /**
     * Contains structures and classes to make a final SSA Graph.
     * SSAGraph- a class with a set of SSANodes and a set of control flows from one SSANode to another.
     *
     * SSANode- a structure which contains the statement command (assign, assert, if, etc.) and the arguments to that
     * statement.
     *
     * SSASubNode- the arguments of SSANode are given by SSASubnodes, which consist of a parent, type of node and a list
     * of arguments.
     */


    struct SSASubNode {
        std::string parent;
        std::string type;

        // args used only if the subnode is a function
        std::vector<std::unique_ptr<SSASubNode>> args;

        void print(const std::string &indent);

        std::string printInLine();

        std::vector<std::string> getVarsReferenced();

        void printAsJSON(std::string indent, std::ostream &outStream);
    };

    struct SSANode {
        std::string cmdName;
        std::string cmd;

        std::vector<std::unique_ptr<SSASubNode>> args;

        std::unique_ptr<SSASubNode> leftChild;
        std::unique_ptr<SSASubNode> rightChild;

        std::string id;

        void print();

        std::string printInLine();

        std::vector<std::string> getVarsReferenced();
        std::string getVarsAssigned();

        void printAsJSON(std::string indent, std::ostream &outStream);

        bool operator<(const SSANode &b) const {
            return id < b.id;
        }
    };

    class SSAGraph {
    private:
        std::map<std::string, std::unique_ptr<SSANode>> nodes;
        std::set<std::pair<std::string, std::string>> control_flow;
        std::string altExitId;

        void generatePrePath(std::vector<std::vector<std::string>>& path, std::string nodeID, std::string terminate, std::set<std::string>& visited);
        std::string generateSMTCond(std::vector<std::string> path, std::string indent, std::map<std::string, std::string> lastAssignedVar);
        std::map<std::string, std::string> generateLastRefVars(std::vector<std::string> path);

    public:
        void addNode(std::unique_ptr<SSANode> &node) {
            nodes[node->id] = (std::move(node));
        }

        std::vector<std::string> getNodeSuccessors(std::string nodeID) {
            std::vector<std::string> successors;
            for(auto pair : control_flow) {
                if(pair.first == nodeID) {
                    successors.push_back(pair.second);
                }
            }

            return successors;
        }

        std::vector<std::string> getNodePredecessors(std::string nodeID) {
            std::vector<std::string> predecessors;
            for(auto pair : control_flow) {
                if(pair.second == nodeID) {
                    predecessors.push_back(pair.first);
                }
            }

            return predecessors;
        }

        std::string getSMT(std::map<std::string, std::set<std::string>>& variables);

        void addFlow(std::string srcid, std::string destid) {
            control_flow.insert(std::pair<std::string, std::string>(srcid, destid));
        }

        std::set<std::pair<std::string, std::string>> &getControlFlow() {
            return control_flow;
        }

        void eraseCtrlFlow(std::pair<std::string, std::string> x) {
            control_flow.erase(x);
        }

        void print();

        void printAsJSON(std::ostream &outStream);

        /**
         * A function to clean the SSAGraph after the entire graph is constructed. Involves removing empty nodes that may
         * have been placed, rerouting control flows as needed and changing some nodes as necessary. Should be removed
         * when the placement function is optimized enough to avoid such placement errors.
         */
        void clean();

        /**
         * A function to simplify the control flow of the SSA Graph in accordance to the simplification provided by Sparrow
         * @return simplified SSA Graph
         */
        SSAGraph simplify();

        void setExitNodeAltID(std::string id) {
            altExitId = std::move(id);
        }

        bool isExitNode(const std::string &id) {
            return altExitId == id;
        }

    };
}

#endif //SSA_TRANSFORM_SSAGRAPH_H
