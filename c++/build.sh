if g++ -fopenmp -o example example.cpp -lz3; then
    echo "Example was successfully compiled."
    echo "To run example, execute:"
    echo "  ./example"
else
    echo "You must install Z3 before compiling this example."
    echo "To install Z3, execute the following command in the Z3 root directory."
    echo "   sudo make install"
fi
