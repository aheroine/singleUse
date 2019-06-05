BUILD_DIR="/home/jl/deploy"
../src/configure  \
LDFLAGS="-L$BUILD_DIR/minisat/build/release/lib/" \
    --with-llvm=$BUILD_DIR/llvm \
#    --with-llvmobj=$BUILD_DIR/llvm/Release \
    --with-stp=$BUILD_DIR/stp/build  \
    --with-llvmcxx=$BUILD_DIR/llvm/Release/bin/clang++  \
    --with-llvmcc=$BUILD_DIR/llvm/Release/bin/clang \
    --with-uclibc=$BUILD_DIR/klee-uclibc \
    --enable-posix-runtime \
    --enable-cxx11

make -j `nproc` ENABLE_OPTIMIZED=1

cp $BUILD_DIR/z3/build/lib/libz3.so ./Release+Asserts/lib/

cd ../..


