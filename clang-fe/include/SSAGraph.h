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

        std::string getSMT(std::map<std::string, std::set<std::string>>& variables) {
            std::string smt;

            std::vector<std::string> orgArgs, auxArgs, assArgs;

            std::set<std::string> usedVars;

            for(auto& node : nodes) {
                for(auto var : node.second->getVarsReferenced()) {
                    usedVars.insert(var.substr(0, var.find_last_of('_')));
                    // llvm::errs() << var << " " << var.substr(0, var.find_last_of('_')) << "\n";
                }
            }

            // find whether we need a tmp variable
            bool tmpNeeded = false;
            for(auto& node : nodes) {
                if (node.second->rightChild != nullptr) {
                    // llvm::errs() << node.second->rightChild->parent << "\n";
                    if (node.second->rightChild->parent == "UNK_VAL") {
                        tmpNeeded = true;
                        break;
                    }
                }
            }

            std::string tmpVar = "tmp";

            smt += "(set-logic LIA)\n\n";

            for(auto var : usedVars) {
                if(tmpNeeded && var == tmpVar) {
                    tmpVar += "0";
                }
                smt += "( declare-const " + var + " Int )\n";
                orgArgs.push_back(var);
                smt += "( declare-const " + var + "! Int )\n";
                auxArgs.push_back(var + "!");
            }

            if(tmpNeeded) {
                smt += "( declare-const " + tmpVar + " Int )\n";
                orgArgs.push_back(tmpVar);
                smt += "( declare-const " + tmpVar + "! Int )\n";
                auxArgs.push_back(tmpVar + "!");
            }

            smt += "\n";

            for(auto var : usedVars) {
                for(auto ssVar : variables[var]) {
                    smt += "( declare-const " + ssVar + " Int )\n";
                    assArgs.push_back(ssVar);
                }
            }

            smt += "\n";

            smt += "( define-fun inv-f( ";

            for(auto arg : orgArgs) {
                smt += "( " + arg + " Int )";
            }

            std::string placeholder = "SPLIT_HERE_asdfghjklzxcvbnmqwertyuiop";

            smt += " ) Bool\n" + placeholder + "\n)\n\n";

            std::set<std::string> visited;

            std::string enter = "ENTRY", exit = "EXIT";
            std::string loopStart, loopEnd;
            for(auto& node : nodes) {
                if(node.second->cmdName == "Loop") {
                    loopStart = node.second->id;
                    break;
                }
            }

            std::string pos = loopStart;
            std::vector<std::string> succs;

            while(true) {
                succs = getNodeSuccessors(pos);

                if(succs.size() == 1) {
                    pos = succs[0];
                } else if(succs.size() == 2) {
                    break;
                }
            }

            std::string loopIf = pos;

            if(succs[0] > succs[1]) {
                loopEnd = getNodeSuccessors(succs[0])[0];
            } else {
                loopEnd = getNodeSuccessors(succs[1])[0];
            }

            std::vector<std::vector<std::string>> path;
            path.emplace_back();
            generatePrePath(path, enter, loopStart, visited);

            auto prepath = std::vector<std::vector<std::string>>(path);

            std::map<std::string, std::string> lastAssignedVar;

            for(auto arg : orgArgs) {
                lastAssignedVar[arg] = arg + "_0";
            }

            // for pre paths

            smt += "( define-fun pre-f ( ";
            for(auto arg: orgArgs) {
                smt += "( " + arg + " Int )";
            }
            for(auto arg: assArgs) {
                smt += "( " + arg + " Int )";
            }

            smt += " ) Bool\n";

            std::string indent = "\t";

            if(path.size() == 1) {
                smt += indent + "( and\n";
                // smt += generateLastRefVars(path[0], variables, indent + "\t");
                auto lastRefMap = generateLastRefVars(path[0]);
                for(auto pair : lastRefMap) {
                    smt += indent + "\t( = " + pair.first + " " + pair.second + " )\n";
                }
                smt += generateSMTCond(path[0], indent + "\t", lastAssignedVar);
                smt += indent + ")\n";
            } else {
                smt += indent + "( or\n";
                indent += "\t";

                for(auto pathBranch : path) {
                    smt += indent + "( and\n";
                    // smt += generateLastRefVars(pathBranch, variables, indent + "\t");
                    auto lastRefMap = generateLastRefVars(pathBranch);
                    for(auto pair : lastRefMap) {
                        smt += indent + "\t( = " + pair.first + " " + pair.second + " )\n";
                    }
                    smt += generateSMTCond(pathBranch, indent + "\t", lastAssignedVar);
                    smt += indent + ")\n";
                }

                indent.pop_back();

                smt += indent + ")\n";
            }

            smt += ")\n\n";


            /*
            for (auto &i : path) {
                for (const auto &j : i) {
                    smt += j + " ";
                }

                smt += "\n";
            }
            smt += "\n";

            for(int i = 0; i < path.size(); i++) {
                smt += "Path " + i + "\n";
                smt += generateSMTCond(path[i]);
            }
             */


            path.erase(path.begin(), path.end());
            visited.erase(visited.begin(), visited.end());
            path.emplace_back();
            std::vector<std::vector<std::string>> phiPath;
            phiPath.emplace_back();
            generatePrePath(phiPath, loopStart, loopIf, visited);

            generatePrePath(path, loopIf, loopEnd, visited);
            // visited.erase(visited.begin(), visited.end());

            // for trans paths

            smt += "( define-fun trans-f ( ";
            for(auto arg: orgArgs) {
                smt += "( " + arg + " Int )";
            }
            for(auto arg: auxArgs) {
                smt += "( " + arg + " Int )";
            }
            for(auto arg: assArgs) {
                smt += "( " + arg + " Int )";
            }

            smt += " ) Bool\n";

            indent = "\t";

            smt += indent + "( or\n";
            indent += "\t";

            smt += indent + "( and\n";
            auto lastRefMap = generateLastRefVars(phiPath[0]);
            auto prepathLastRefMap = generateLastRefVars(prepath[0]);

            for(auto pair : lastRefMap) {
                smt += indent + "\t( = " + pair.second + " " + pair.first + " )\n";
                lastAssignedVar[pair.first] = pair.second;
            }
            for(auto pair : lastRefMap) {
                smt += indent + "\t( = " + pair.second + " " + pair.first + "! )\n";
            }

            auto loopCondVars = nodes[loopIf]->getVarsReferenced();

            for(auto& var : loopCondVars){
                std::string varRoot = var.substr(0, var.find_last_of('_'));

                llvm::errs() << var << " " << varRoot << " " << (lastRefMap[varRoot] == "") << "\n";

                if(lastRefMap[varRoot] == "") {
                    smt += indent + "\t( = " + varRoot + " " + var + " )\n";
                    smt += indent + "\t( = " + varRoot + "! " + var + " )\n";
                }

                var = varRoot;
            }

            for(auto var : usedVars) {
                if(std::find(loopCondVars.begin(), loopCondVars.end(), var) == loopCondVars.end()) {
                    // variable not found in condition
                    smt += indent + "\t( = " + var + " " + var + "! )\n";
                }
            }

            if(tmpNeeded) {
                smt += indent + "\t(= " + tmpVar + " " + tmpVar + "! )\n";
            }

            smt += indent + ")\n";

            for(int i = 0; i < path.size() - 1; i++) {

                // std::set<std::string> refVar;
                std::set<std::string> assVar;

                for(auto node : path[i]) {
//                    for(auto var : nodes[node]->getVarsReferenced()) {
//                        refVar.insert(var.substr(0, var.find_last_of('_')));
//                    }
                    std::string assvar = nodes[node]->getVarsAssigned();
                    if(assvar != "")
                        assVar.insert(assvar.substr(0, assvar.find_last_of('_')));
                }

                smt += indent + "( and\n";
                for(auto pair : lastRefMap) {
                    if(std::find(assVar.begin(), assVar.end(), pair.first) != assVar.end()) {
                        smt += indent + "\t( = " + pair.second + " " + pair.first + " )\n";
                    }
                }
                smt += generateSMTCond(path[i], indent + "\t", lastAssignedVar);
                auto pathBranchLastRef = generateLastRefVars(path[i]);
                for(auto pair : pathBranchLastRef) {
                    if(std::find(assVar.begin(), assVar.end(), pair.first) != assVar.end())
                        smt += indent + "\t( = " + pair.second + " " + pair.first + "! )\n";
                }

                std::set<std::string> unrefVar;

                std::set_difference(usedVars.begin(), usedVars.end(), assVar.begin(), assVar.end(), std::inserter(unrefVar, unrefVar.end()));

                for(auto i : unrefVar) {
                    std::string newI = prepathLastRefMap[i];
                    if(newI.empty()) {
                        newI = i + "_0";
                    }
                    smt += indent + "\t(= " + i + " " + newI + " )\n";
                    smt += indent + "\t(= " + i + "! " + newI + " )\n";
                }

                if(tmpNeeded) {
                    smt += indent + "\t(= " + tmpVar + " " + tmpVar + "! )\n";
                }

                smt += indent + ")\n";
            }

            indent.pop_back();
            smt += indent + ")\n";
            smt += ")\n\n";


            /*
            for (auto &i : path) {
                for (const auto &j : i) {
                    smt += j + " ";
                }

                smt += "\n";
            }
            smt += "\n";
            for (const auto &j : phiPath[0]) {
                smt += j + " ";
            }

            smt += "\n";

            for(int i = 0; i < path.size(); i++) {
                smt += "Path " + i + "\n";
                smt += generateSMTCond(path[i]);
            }
             */

            path.erase(path.begin(), path.end());
            visited.erase(visited.begin(), visited.end());
            path.emplace_back();
            generatePrePath(path, loopEnd, exit, visited);

            auto assertPath = std::vector<std::vector<std::string>>();

            for(auto branch : path) {
                for(auto node : branch) {
                    if(nodes[node]->cmdName == "Assert") {
                        assertPath.push_back(branch);
                        break;
                    }
                }
            }

            smt += "( define-fun post-f ( ";
            for(auto arg: orgArgs) {
                smt += "( " + arg + " Int )";
            }
            for(auto arg: assArgs) {
                smt += "( " + arg + " Int )";
            }

            smt += " ) Bool\n";

            indent = "\t";

            if(assertPath.size() > 1) {
                smt += indent + "( and\n";
                indent += "\t";
            }

            for(auto branch: prepath) {
                for(auto refVar : generateLastRefVars(branch)) {
                    if(lastRefMap[refVar.first].empty()) {
                        lastRefMap[refVar.first] = refVar.second;
                    }
                }
            }

            for(auto pathBranch : assertPath) {

                smt += indent + "( or\n";
                indent += "\t";
                smt += indent + "( not\n";
                indent += "\t";

                if(lastRefMap.size() > 1) {
                    smt += indent + "( and\n";
                    indent += "\t";
                    for(auto var : usedVars) {
                        if(lastRefMap[var].empty()) {
                            smt += indent + "( = " + var + " " + var + "_0 )\n";
                        } else {
                            smt += indent + "( = " + var + " " + lastRefMap[var] + ")\n";
                        }
                    }
                    indent.pop_back();
                    smt += indent + ")\n";
                } else if(lastRefMap.size() == 1) {
                    smt += indent + "( = " + lastRefMap.begin()->first + " " + lastRefMap.begin()->second + ")\n";
                }

                indent.pop_back();

                smt += indent + ")\n";


                smt += indent + "( not\n";
                indent += "\t";
                smt += indent + "( and\n";
                indent += "\t";

                std::string ifSMT = nodes[loopIf]->printInLine();

                if(!ifSMT.empty()) {
                    smt += indent + "( not " + ifSMT + " )\n";
                }
                smt += generateSMTCond(pathBranch, indent, lastAssignedVar);
                indent.pop_back();
                smt += indent + ")\n";
                indent.pop_back();
                smt += indent + ")\n";
                indent.pop_back();
                smt += indent + ")\n";
            }

            if(assertPath.size() > 1) {
                indent.pop_back();
                smt += indent + ")\n";
            }

            indent.pop_back();

            smt += indent + ")\n";
            // smt += ")\n";

            /*
            for (auto &i : path) {
                for (const auto &j : i) {
                    smt += j + " ";
                }

                smt += "\n";
            }
            smt += "\n";

            for(int i = 0; i < path.size(); i++) {
                smt += "Path " + i + "\n";
                smt += generateSMTCond(path[i]);
            }
             */

            // at the end
            smt += placeholder + "\n" + "( assert ( not\n";
            indent = "\t";
            smt += indent + "( =>\n";
            indent += "\t";

            smt += indent + "( pre-f ";
            for(auto arg : orgArgs) {
                smt += arg + " ";
            }
            for(auto arg : assArgs) {
                smt += arg + " ";
            }
            smt += " )\n";

            smt += indent + "( inv-f ";
            for(auto arg : orgArgs) {
                smt += arg + " ";
            }
            smt += ")\n";

            indent.pop_back();
            smt += indent + ")\n";
            smt += "))\n\n";


            smt += placeholder + "\n" + "( assert ( not\n";
            indent = "\t";
            smt += indent + "( =>\n";
            indent += "\t";
            smt += indent + "( and\n";
            indent += "\t";
            smt += indent + "( inv-f ";
            for(auto arg : orgArgs) {
                smt += arg + " ";
            }
            smt += ")\n";
            smt += indent + "( trans-f ";
            for(auto arg : orgArgs) {
                smt += arg + " ";
            }
            for(auto arg : auxArgs) {
                smt += arg + " ";
            }
            for(auto arg : assArgs) {
                smt += arg + " ";
            }
            smt += ")\n";

            indent.pop_back();
            smt += indent + ")\n";

            smt += indent + "( inv-f ";
            for(auto arg : auxArgs) {
                smt += arg + " ";
            }
            smt += ")\n";

            indent.pop_back();
            smt += indent + ")\n";
            smt += "))\n\n";

            smt += placeholder + "\n" + "( assert ( not\n";
            indent = "\t";
            smt += indent + "( =>\n";
            indent += "\t";

            smt += indent + "( inv-f ";
            for(auto arg : orgArgs) {
                smt += arg + " ";
            }
            smt += " )\n";

            smt += indent + "( post-f ";
            for(auto arg : orgArgs) {
                smt += arg + " ";
            }
            for(auto arg : assArgs) {
                smt += arg + " ";
            }
            smt += ")\n";

            indent.pop_back();
            smt += indent + ")\n";
            smt += "))\n\n";

            return smt;

        }

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
