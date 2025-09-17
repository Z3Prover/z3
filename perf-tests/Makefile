CXX = g++
CXXFLAGS = -O2 -std=c++17 -I../src
LDFLAGS = -L../build
LIBS = -lz3

all: ast_allocation_bench

ast_allocation_bench: ast_allocation_bench.cpp
	$(CXX) $(CXXFLAGS) -o $@ $< $(LDFLAGS) $(LIBS)

clean:
	rm -f ast_allocation_bench

.PHONY: all clean