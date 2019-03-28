CPPFLAGS=-Iinclude $(shell llvm-config-7 --cxxflags) -ggdb

CLANGLIBS=-lclangTooling -lclangFrontendTool -lclangFrontend -lclangDriver -lclangSerialization -lclangCodeGen -lclangParse -lclangSema -lclangStaticAnalyzerFrontend -lclangStaticAnalyzerCheckers -lclangStaticAnalyzerCore -lclangAnalysis -lclangARCMigrate -lclangRewrite -lclangRewriteFrontend -lclangEdit -lclangAST -lclangLex -lclangBasic -lclang

LDFLAGS=$(shell llvm-config-7 --ldflags --system-libs --libs core native engine) $(CLANGLIBS)

CC=clang++-7

.PHONY: all tests clean

all: bin/clang-fe

bin/clang-fe: obj/Rewriter.o obj/domfrontier.o obj/MainVisitor.o obj/SSAGraph.o obj/SSAWriter.o obj/main.o
	@mkdir -p bin/
	@echo prereqs that are newer than bin/clang-fe: $?
	$(CC) obj/Rewriter.o obj/domfrontier.o obj/MainVisitor.o obj/SSAGraph.o obj/SSAWriter.o obj/main.o $(LDFLAGS) -o bin/clang-fe


obj/Rewriter.o : src/Rewriter.cpp include/Rewriter.h
	@mkdir -p obj/
	@echo prereqs that are newer than obj/Rewriter.o: $?
	$(CC) -c $(CPPFLAGS) -O3 src/Rewriter.cpp -o obj/Rewriter.o


obj/MainVisitor.o : src/MainVisitor.cpp include/MainVisitor.h
	@mkdir -p obj/
	@echo prereqs that are newer than obj/MainVisitor.o: $?
	$(CC) -c $(CPPFLAGS) -O3 src/MainVisitor.cpp -o obj/MainVisitor.o


obj/domfrontier.o : src/domfrontier.cpp include/domfrontier.h
	@mkdir -p obj/
	@echo prereqs that are newer than obj/domfrontier.o: $?
	$(CC) -c $(CPPFLAGS) -O3 src/domfrontier.cpp -o obj/domfrontier.o


obj/SSAGraph.o : src/SSAGraph.cpp include/SSAGraph.h
	@mkdir -p obj/
	@echo prereqs that are newer than obj/SSAGraph.o: $?
	$(CC) -c $(CPPFLAGS) -O3 src/SSAGraph.cpp -o obj/SSAGraph.o


obj/SSAWriter.o : src/SSAWriter.cpp include/SSAWriter.h obj/SSAGraph.o
	@mkdir -p obj/
	@echo prereqs that are newer than obj/SSAWriter.o: $?
	$(CC) -c $(CPPFLAGS) -O3 src/SSAWriter.cpp -o obj/SSAWriter.o


obj/main.o : src/main.cpp 
	@mkdir -p obj/
	@echo prereqs that are newer than obj/main.o: $?
	$(CC) -c $(CPPFLAGS) -O3 src/main.cpp -o obj/main.o


tests: bin/clang-fe
	@echo "The tests need to be manually verified. The json files are written into the same directory as the test cases."
	@echo "For information about the rewritten code, CFG and the Dominator Tree, run make test-debug."
	@cp tests/assert.h .
	./bin/clang-fe -ssa $(shell ls tests/*.c) 2>/dev/null
	@rm assert.h

test-debug: bin/clang-fe
	@echo "The tests need to be manually verified. The json files are written into the same directory as the test cases."
	@echo "For information about the rewritten code, CFG and the Dominator Tree, run make test-debug."
	@cp tests/assert.h .
	./bin/clang-fe -ssa $(shell ls tests/*.c)
	@rm assert.h

clean:
	rm -rf obj/ bin/