if gcc -fopenmp -o test_capi test_capi.c -lz3; then
    echo "test_capi applicatio was successfully compiled."
    echo "To try it, execute:"
    echo "  ./test_capi"
else
    echo "You must install Z3 before compiling this example."
    echo "To install Z3, execute the following command in the Z3 root directory."
    echo "   sudo make install"
fi
