if gcc -fopenmp -o maxsat maxsat.c -lz3; then
    echo "maxsat example was successfully compiled."
    echo "To run example, execute:"
    echo "  ./maxsat ex.smt"
else
    echo "You must install Z3 before compiling this example."
    echo "To install Z3, execute the following command in the Z3 root directory."
    echo "   sudo make install"
fi
