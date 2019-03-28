#include "../include/SSAGraph.h"

namespace ssa_transform {
    void SSASubNode::print(const std::string &indent) {
        llvm::errs() << indent << type << " : " << parent << "\n";

        for (auto &arg : args) {
            arg->print(indent + "\t");
        }

        llvm::errs() << "\n";
    }

    void SSASubNode::printAsJSON(std::string indent, std::ostream &outStream) {
        outStream << indent << "\"" << type << "\": \"" << parent << "\"";
        if (!args.empty()) {
            outStream << ",\n";
            int i;
            for (i = 0; i < args.size() - 1; i++) {
                outStream << indent << "\"arg" << i << "\": {\n";
                args[i]->printAsJSON(indent + "\t", outStream);
                outStream << indent << "},\n";
            }

            outStream << indent << "\"arg" << i << "\": {\n";
            args[i]->printAsJSON(indent + "\t", outStream);
            outStream << indent << "}";
        }
        outStream << "\n";
    }

    void SSANode::print() {

        llvm::errs() << id << "\n";
        llvm::errs() << cmdName << "\n";

        if (cmdName == "Assert" || cmdName == "Assume" || cmdName == "func_call") {
            for (auto &arg : args) {
                arg->print("\t");
            }
        }

        if (leftChild != nullptr) {
            leftChild->print("\t");
        }

        if (rightChild != nullptr) {
            rightChild->print("\t");
        }

        llvm::errs() << "\n----------------------------------------------------------\n";
    }

    void SSANode::printAsJSON(std::string indent, std::ostream &outStream) {
        outStream << indent << "\"" << id << "\": {\n";
        outStream << indent << "\t\"cmd\": \"" << cmdName << "\"";

        if (leftChild != nullptr) {
            outStream << ",\n";
            outStream << indent << "\t\"lval\": {\n";
            leftChild->printAsJSON(indent + "\t\t", outStream);
            outStream << indent << "\t}";
        }

        if (rightChild != nullptr) {
            outStream << ",\n";
            outStream << indent << "\t\"rval\": {\n";
            rightChild->printAsJSON(indent + "\t\t", outStream);
            outStream << indent << "\t}";
        } else if (!args.empty() && (cmdName == "Assert" || cmdName == "Assume")) {
            outStream << ",\n";
            outStream << indent << "\t\"rval\": {\n";
            args[0]->printAsJSON(indent + "\t\t", outStream);
            outStream << indent << "\t}";
        } else if (!args.empty() && (cmdName == "func_call" || cmdName == "UNK")) {
            outStream << ",\n";
            outStream << indent << "\t\"rval\": {\n";
            int i;
            for (i = 0; i < args.size() - 1; i++) {
                outStream << indent << "\t\"arg" << i << "\": {\n";
                args[i]->printAsJSON(indent + "\t\t", outStream);
                outStream << indent << "\t},\n";
            }

            outStream << indent << "\t\"arg" << i << "\": {\n";
            args[i]->printAsJSON(indent + "\t\t", outStream);
            outStream << indent << "\t}";
        }

        outStream << "\n" << indent << "}";
    }

    void SSAGraph::print() {
        for (const auto &node : nodes) {
            node.second->print();
        }
        for (const auto &pair : control_flow) {
            llvm::errs() << pair.first << " -> " << pair.second << "\n";
        }
    }

    /**
     * printAsJSON prints the SSAGraph in a JSON format into an outstream (either cout or ofstream if needed to print
     * into a file).
     * Currently every node is printed on a new line, regardless if it has more arguments.
     *
     * @todo Edit the function so that nodes without arguments can be printed on the same line for conciseness.
     *
     * @param indent
     * @param outStream
     */
    void SSAGraph::printAsJSON(std::ostream &outStream) {
        outStream << "{\n";
        outStream << "\t\"nodes\": {\n";
        int i = 0;
        for (const auto &node : nodes) {
            if (i < nodes.size() - 1) {
                node.second->printAsJSON("\t\t", outStream);
                outStream << ",\n";
                i++;
            } else {
                break;
            }
        }

        (*nodes.rbegin()).second->printAsJSON("\t\t", outStream);

        outStream << "\n\t},\n";
        outStream << "\t\"control-flow\": [\n";
        i = 0;
        for (const auto &pair : control_flow) {
            if (i < control_flow.size() - 1) {
                outStream << "\t\t[ ";
                outStream << "\"" << pair.first << "\", \"" << pair.second << "\" ],\n";
                i++;
            } else {
                break;
            }
        }

        auto lastPair = (*control_flow.rbegin());

        outStream << "\t\t[ ";
        outStream << "\"" << lastPair.first << "\", \"" << lastPair.second << "\" ]\n";

        outStream << "\t]\n}\n";

    }



    void SSAGraph::generatePrePath(std::vector<std::vector<std::string>>& path, std::string nodeID, std::string terminate, std::set<std::string>& visited) {

        if(visited.find(nodeID) == visited.end() && nodeID != terminate) {
            visited.insert(nodeID);
            std::vector<std::string> successors;
            std::vector<std::string> predecessors;
            std::string command;

            /*for (const auto &node : nodes) {
                if (node.first == nodeID) {
                    command = node.second->cmdName;
                    break;
                }
            }*/

            command = nodes[nodeID]->cmdName;

            for (auto pair : control_flow) {
                if (pair.first == nodeID) {
                    successors.push_back(pair.second);
                } else if (pair.second == nodeID) {
                    predecessors.push_back(pair.first);
                }
            }

            if (successors.size() == 1) {
                for (auto &paths : path) {
                    paths.push_back(nodeID);
                }

                generatePrePath(path, successors[0], terminate, visited);
            } else {
                for (auto &paths : path) {
                    paths.push_back(nodeID);
                }
                std::vector<std::vector<std::string>> subpath1, subpath2;
                subpath1.emplace_back();
                subpath2.emplace_back();

                auto subpath1visited = visited;
                auto subpath2visited = visited;

                generatePrePath(subpath1, successors[0], terminate, subpath1visited);
                generatePrePath(subpath2, successors[1], terminate, subpath2visited);

                auto currentPath = std::vector<std::vector<std::string>>(path);

                path.erase(path.begin(), path.end());

                for (auto currentPaths : currentPath) {
                    for (auto subpath : subpath1) {
                        std::vector<std::string> p;
                        for (auto elem : currentPaths) {
                            p.push_back(elem);
                        }
                        for (auto elem: subpath) {
                            p.push_back(elem);
                        }

                        path.push_back(p);
                    }
                    for (auto subpath : subpath2) {
                        std::vector<std::string> p;
                        for (auto elem : currentPaths) {
                            p.push_back(elem);
                        }
                        for (auto elem: subpath) {
                            p.push_back(elem);
                        }

                        path.push_back(p);
                    }
                }
            }
            /*
            std::vector<std::string> successors;
            std::vector<std::string> predecessors;
            std::string command;

            for(const auto& node : nodes) {
                if(node->id == nodeID) {
                    command = node->cmdName;
                    break;
                }
            }

            for(auto pair : control_flow) {
                if(pair.first == nodeID) {
                    successors.push_back(pair.second);
                } else if(pair.second == nodeID) {
                    predecessors.push_back(pair.first);
                }
            }


            llvm::errs() << "Considering " << nodeID << "\n" << "Predecessors " << predecessors.size() << "\n";

            visited[nodeID]++;

            if(command == "Loop") {
                return;
            } else if(visited[nodeID] == 1) {
                if (predecessors.size() > 1) {
                    return;
                } else {

                    indent.push_back(currentIndent);

                    if(successors.size() > 1) {
                        currentIndent += 1;
                    }

                    path.push_back(nodeID);

                    for(auto successor : successors) {
                        generatePrePath(path, visited, successor, indent, currentIndent);
                    }
                }
            } else if(visited[nodeID] > 1) {
                if(predecessors.size() > 1) {
                    currentIndent -= 1;
                    if (visited[nodeID] == predecessors.size()) {
                        indent.push_back(currentIndent);
                        path.push_back(nodeID);
                        for (auto successor: successors) {
                            generatePrePath(path, visited, successor, indent, currentIndent);
                        }
                    } else {
                        return;
                    }
                }
            }
             */
        }
    }


    /**
     * A function to clean the SSAGraph after the entire graph is constructed. Involves removing empty nodes that may
     * have been placed, rerouting control flows as needed and changing some nodes as necessary.
     *
     * @todo Remove the function and incorporate the cleaning functionalities into the SSA printSeqCFGStmt.
     */

    void SSAGraph::clean() {
        // makes sure no empty nodes remain

        for (const auto &node : nodes) {
            if (node.second->cmdName.empty()) {
                // If the node is an empty node

                // llvm::errs() << "Considering " << node->id << "\n";
                std::list<std::string> inedgeSrc, outedgeDest;
                auto ctrlFlowCopy = control_flow;
                for (auto pair: ctrlFlowCopy) {
                    // llvm::errs() << "Flow " << pair.first << "->" << pair.second << "\n";
                    if (pair.second == node.first) {
                        inedgeSrc.push_back(pair.first);
                        control_flow.erase(pair);
                        // llvm::errs() << "Removed " << pair.first << "->" << pair.second << "\n";
                    } else if (pair.first == node.first) {
                        outedgeDest.push_back(pair.second);
                        control_flow.erase(pair);
                        // llvm::errs() << "Removed " << pair.first << "->" << pair.second << "\n";
                    }
                }

                if (inedgeSrc.size() == 1 && outedgeDest.size() == 2) {
                    // this means that src is an the condition inside the if statement represented by the current node and branches out
                    // occurs in cases when the if condition is just a function call, like if(__Verifier_nondet_int())

                    for (auto &nodeToReplace : nodes) {
                        if (nodeToReplace.first == *inedgeSrc.begin()) {
                            auto newNode = llvm::make_unique<SSANode>();
                            newNode->id = nodeToReplace.first;
                            newNode->cmdName = "if";
                            newNode->rightChild = llvm::make_unique<SSASubNode>();
                            newNode->rightChild->type = nodeToReplace.second->cmdName;
                            newNode->rightChild->parent = nodeToReplace.second->cmd;
                            if (nodeToReplace.second->leftChild != nullptr) {
                                newNode->rightChild->args.push_back(std::move(nodeToReplace.second->leftChild));
                            }

                            if (nodeToReplace.second->rightChild != nullptr) {
                                newNode->rightChild->args.push_back(std::move(nodeToReplace.second->rightChild));
                            } else if (!nodeToReplace.second->args.empty()) {
                                for (auto &arg : nodeToReplace.second->args) {
                                    newNode->rightChild->args.push_back(std::move(arg));
                                }
                            }

                            nodes.erase(nodeToReplace.first);
                            nodes[newNode->id] = (std::move(newNode));
                            break;
                        }
                    }
                }

                for (auto srcNode : inedgeSrc) {
                    for (auto destNode : outedgeDest) {
                        control_flow.insert(std::make_pair(srcNode, destNode));
                        // llvm::errs() << "Inserted " << srcNode << "->" << destNode << "\n";
                    }
                }

                nodes.erase(node.first);
            }
        }
    }

    SSAGraph SSAGraph::simplify() {

    }

    std::string SSASubNode::printInLine() {
        std::string res;
        if(type == "OP") {
            if(args.size() == 1) {
                return "( " + parent + args[0]->printInLine() + " )";
            } else {
                std::string op = parent;
                if(parent == "==") {
                    op = "=";
                    return "( " + op + " " + args[0]->printInLine() + " " + args[1]->printInLine() + " )";
                } else if(parent == "!=") {
                    op = "=";
                    return "( not ( " + op + " " + args[0]->printInLine() + " " + args[1]->printInLine() + " ) )";
                } else if(parent == "!") {
                    return "( not " + args[0]->printInLine() + " )";
                }
                return "( " + op + " " + args[0]->printInLine() + " " + args[1]->printInLine() + " )";
            }
        } else if(type == "Var" || type == "Const") {
            return parent;
        } else {
            return "";
        }
    }

    std::string SSANode::printInLine() {
        std::string l = "";

        if(leftChild != nullptr) {
            l = leftChild->printInLine();
        }

        std::string r = "";

        if(rightChild != nullptr) {
            r = rightChild->printInLine();
        }

        if(cmdName == "assign") {
            return "= " + l + " " + r;
        } else if(cmdName == "if") {
            return l + r;
        } else if(cmdName == "Assert") {
            return "not " + args[0]->printInLine();
        } else if(cmdName == "Assume") {
            return args[0]->printInLine();
        } else {
            return ""; //l + cmdName + r;
        }
    }

    std::string SSAGraph::generateSMTCond(std::vector<std::string> path, std::string indent, std::map<std::string, std::string> lastAssignedVar) {
        std::string res = "";
        std::string conditionNode = "";
        for(const auto& node : path) {
            if(nodes[node]->cmdName == "assign") {
                auto var = nodes[node]->leftChild->parent;
                auto varRoot = var.substr(0, var.find_last_of('_'));

                lastAssignedVar[varRoot] = var;
            } else if(nodes[node]->cmdName == "Phi") {
                auto var = nodes[node]->leftChild->parent;
                auto varRoot = var.substr(0, var.find_last_of('_'));

                res += indent + "( = " + var + " " + lastAssignedVar[varRoot] + " )\n";

                lastAssignedVar[varRoot] = var;
            }

            if(nodes[node]->cmdName == "if") {
                conditionNode = node;
            } else if(nodes[node]->cmdName == "TrueBranch") {
                std::string smtCond = nodes[conditionNode]->printInLine();
                if(!smtCond.empty()) {
                    res += indent + smtCond + "\n";
                }
            } else if(nodes[node]->cmdName == "FalseBranch") {
                std::string smtCond = nodes[conditionNode]->printInLine();
                if(!smtCond.empty()) {
                    res += indent + "( not " + smtCond + " )\n";
                }
            } else if(nodes[node]->cmdName == "Assume") {
                std::string smtCond = nodes[node]->printInLine();
                if(!smtCond.empty()) {
                    res += indent + smtCond + "\n";
                }
            } else {
                std::string s = nodes[node]->printInLine();
                if(!s.empty()) {
                    res += indent + "( " + s + " )\n";
                }
            }
        }

        return res;
    }

    std::vector<std::string> SSASubNode::getVarsReferenced() {
        std::vector<std::string> vars;

        if(type == "Var") {
            vars.push_back(parent);
        } else {
            for(auto& arg : args) {
                for(auto var : arg->getVarsReferenced()) {
                    vars.push_back(var);
                }
            }
        }

        return vars;
    }

    std::vector<std::string> SSANode::getVarsReferenced() {
        std::vector<std::string> vars;
        if(leftChild != nullptr) {
            auto v = leftChild->getVarsReferenced();
            for(auto var : v) {
                vars.push_back(var);
            }
        }

        if(rightChild != nullptr) {
            auto v = rightChild->getVarsReferenced();
            for(auto var : v) {
                vars.push_back(var);
            }
        }

        for(auto& arg : args) {
            for(auto var : arg->getVarsReferenced()) {
                vars.push_back(var);
            }
        }

        return vars;
    }

    std::string SSANode::getVarsAssigned() {
        if(cmdName == "assign" || cmdName == "Phi") {
            return leftChild->parent;
        } else {
            return "";
        }
    }

    std::map<std::string, std::string> SSAGraph::generateLastRefVars(std::vector<std::string> path) {
        std::map<std::string, std::string> referencedVars;
        std::string res;

        for(auto node : path) {
            auto refVar = nodes[node]->getVarsReferenced();
            for(auto revIter = refVar.rbegin(); revIter != refVar.rend(); revIter++) {
                std::string rootVar = revIter->substr(0, revIter->find_last_of("_"));
                referencedVars[rootVar] = *revIter;
            }

        }

        return referencedVars;
    }

    std::string SSAGraph::getSMT(std::map<std::string, std::set<std::string>>& variables) {
        std::string smt;

        std::vector<std::string> orgArgs, auxArgs, assArgs;

        std::set<std::string> usedVars;

        for(auto& node : nodes) {
            for(auto var : node.second->getVarsReferenced()) {
                usedVars.insert(var.substr(0, var.find_last_of('_')));
            }
        }

        // find whether we need a tmp variable
        bool tmpNeeded = false;
        for(auto& node : nodes) {
            if (node.second->rightChild != nullptr) {
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


        path.erase(path.begin(), path.end());
        visited.erase(visited.begin(), visited.end());
        path.emplace_back();
        std::vector<std::vector<std::string>> phiPath;
        phiPath.emplace_back();
        generatePrePath(phiPath, loopStart, loopIf, visited);

        generatePrePath(path, loopIf, loopEnd, visited);

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

            if(lastRefMap[varRoot] == "") {
                smt += indent + "\t( = " + varRoot + " " + var + " )\n";
                smt += indent + "\t( = " + varRoot + "! " + var + " )\n";
            }

            var = varRoot;
        }

        for(auto var : usedVars) {
            if(std::find(loopCondVars.begin(), loopCondVars.end(), var) == loopCondVars.end()) {
                smt += indent + "\t( = " + var + " " + var + "! )\n";
            }
        }

        if(tmpNeeded) {
            smt += indent + "\t(= " + tmpVar + " " + tmpVar + "! )\n";
        }

        smt += indent + ")\n";

        for(int i = 0; i < path.size() - 1; i++) {

            std::set<std::string> assVar;

            for(auto node : path[i]) {
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
}