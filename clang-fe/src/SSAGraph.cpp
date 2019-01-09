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

        if (cmdName == "Assert" || cmdName == "func_call") {
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
        } else if (!args.empty() && cmdName == "Assert") {
            outStream << ",\n";
            outStream << indent << "\t\"rval\": {\n";
            args[0]->printAsJSON(indent + "\t\t", outStream);
            outStream << indent << "\t}";
        } else if (!args.empty() && cmdName == "func_call") {
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
            node->print();
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
                node->printAsJSON("\t\t", outStream);
                outStream << ",\n";
                i++;
            } else {
                break;
            }
        }

        (*nodes.rbegin())->printAsJSON("\t\t", outStream);

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


    /**
     * A function to clean the SSAGraph after the entire graph is constructed. Involves removing empty nodes that may
     * have been placed, rerouting control flows as needed and changing some nodes as necessary.
     *
     * @todo Remove the function and incorporate the cleaning functionalities into the SSA printSeqCFGStmt.
     */

    void SSAGraph::clean() {
        // makes sure no empty nodes remain

        for (const auto &node : nodes) {
            if (node->cmdName.empty()) {
                // If the node is an empty node

                // llvm::errs() << "Considering " << node->id << "\n";
                std::list<std::string> inedgeSrc, outedgeDest;
                auto ctrlFlowCopy = control_flow;
                for (auto pair: ctrlFlowCopy) {
                    // llvm::errs() << "Flow " << pair.first << "->" << pair.second << "\n";
                    if (pair.second == node->id) {
                        inedgeSrc.push_back(pair.first);
                        control_flow.erase(pair);
                        // llvm::errs() << "Removed " << pair.first << "->" << pair.second << "\n";
                    } else if (pair.first == node->id) {
                        outedgeDest.push_back(pair.second);
                        control_flow.erase(pair);
                        // llvm::errs() << "Removed " << pair.first << "->" << pair.second << "\n";
                    }
                }

                if (inedgeSrc.size() == 1 && outedgeDest.size() == 2) {
                    // this means that src is an the condition inside the if statement represented by the current node and branches out
                    // occurs in cases when the if condition is just a function call, like if(__Verifier_nondet_int())

                    for (auto &nodeToReplace : nodes) {
                        if (nodeToReplace->id == *inedgeSrc.begin()) {
                            auto newNode = llvm::make_unique<SSANode>();
                            newNode->id = nodeToReplace->id;
                            newNode->cmdName = "if";
                            newNode->rightChild = llvm::make_unique<SSASubNode>();
                            newNode->rightChild->type = nodeToReplace->cmdName;
                            newNode->rightChild->parent = nodeToReplace->cmd;
                            if (nodeToReplace->leftChild != nullptr) {
                                newNode->rightChild->args.push_back(std::move(nodeToReplace->leftChild));
                            }

                            if (nodeToReplace->rightChild != nullptr) {
                                newNode->rightChild->args.push_back(std::move(nodeToReplace->rightChild));
                            } else if (!nodeToReplace->args.empty()) {
                                for (auto &arg : nodeToReplace->args) {
                                    newNode->rightChild->args.push_back(std::move(arg));
                                }
                            }

                            nodes.erase(nodeToReplace);
                            nodes.insert(std::move(newNode));
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

                nodes.erase(node);
            }
        }
    }


}