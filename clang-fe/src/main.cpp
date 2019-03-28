// ssa-transform/main.cpp
// Author- Aaditya Naik

/**
 * General Procedure-
 *
 * Given a c file as an argument, the tool makes 3 passes over the code. The first pass involves Rewriter.h, which rewrites
 * the code so that certain complex statements are simplified and can be used with the remainder of the ssa-transform
 *
 * The second pass involves MainVisitor.h, which visits the statements in the main function and makes several maps which
 * help identify the variables, their locations and their replacements
 *
 * The third pass involves SSAWriter.h which constructs the SSA graph using the maps made by MainVisitor. This SSA graph
 * can then be printed either using the print method or the printAsJSON method.
 *
 * We define an AST Consumer and an AST Frontend to give the AST context to the RecursiveASTVisitor
 *     following the guidelines at https://clang.llvm.org/docs/RAVFrontendAction.html
 */

#include <fstream>
#include <string>
#include <iostream>
#include <vector>
#include <exception>
#include <unordered_set>
#include <future>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/APFloat.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/AST/Stmt.h"
#include "clang/Analysis/CFGStmtMap.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/Expr.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "clang/Lex/Lexer.h"

#include "../include/domfrontier.h"
#include "../include/Rewriter.h"
#include "../include/MainVisitor.h"
#include "../include/SSAWriter.h"
#include "../include/SSAGraph.h"

using namespace clang;
using namespace ssa_transform;

int main(int argc, const char **argv) {
    if(argc > 2) {
        std::string mode = argv[1];
        for(int i = 2; i < argc; i++) {
            // argv[i] denotes the file name, content is the file's contents ie the code
            // we handle only 1 argument as of this point
            // gives a segfault if no files of the name exist
            std::ifstream inputFile(argv[i]);
            std::string content( (std::istreambuf_iterator<char>(inputFile)), (std::istreambuf_iterator<char>()));

            // The only way I could figure out to get variables affected by the Recursive AST Visitor was to pass those variables
            // by reference into the FrontEndAction classes and then retrieve the values when the pass was finished.

            // FIRST PASS- REWRITING THE CONTENTS
            auto * rewriterClassAction = new ssa_transform::RewriterClassAction();
            std::string newContent;
            rewriterClassAction->setRewrittenContentsAddress(newContent);

            clang::tooling::runToolOnCode(rewriterClassAction, content);

            llvm::errs() << "Rewritten code is\n\n" << newContent << "\n";

            // SECOND PASS- GETTING THE NECESSARY DATA STRUCTURES
            std::map<clang::SourceLocation, std::string> resVarReplacementMap;
            std::map<int, std::list<std::pair<std::string, std::vector<std::string>>>> phiPlacementMap;
            std::map<std::string, std::set<std::string>> variableMap;

            auto * mainClassAction = new ssa_transform::MainClassAction();

            mainClassAction->setReplacementMap(resVarReplacementMap);
            mainClassAction->setPhiPlaceMap(phiPlacementMap);
            mainClassAction->setVariableMap(variableMap);

            clang::tooling::runToolOnCode(mainClassAction, newContent);

            auto * ssaWriterFrontEndAction = new SSAWriterFrontAction(
                    resVarReplacementMap, phiPlacementMap, variableMap, argv[i], mode);

            // THIRD PASS- MAKING THE SSA GRAPH
            clang::tooling::runToolOnCode(ssaWriterFrontEndAction, newContent);

        }
    }

    return 0;
}
