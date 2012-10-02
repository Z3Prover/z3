# Note: Z3 was built using C++, so libz3.a has C++ dependencies. 
#       You can use gcc to link the program, but you need tell it 
#       to link the C++ libraries
g++ -fopenmp -I../../include test_capi.c ../../lib/libz3.a -o test_capi
