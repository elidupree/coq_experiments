#!/bin/bash

# EliDupree's note: copied and slightly modified from rust-autograd https://github.com/raskr/rust-autograd/blob/master/examples/download_mnist.sh
curl http://yann.lecun.com/exdb/mnist/train-images-idx3-ubyte.gz --output "$1/train-images-idx3-ubyte.gz"
curl http://yann.lecun.com/exdb/mnist/train-labels-idx1-ubyte.gz --output "$1/train-labels-idx1-ubyte.gz"
curl http://yann.lecun.com/exdb/mnist/t10k-images-idx3-ubyte.gz --output "$1/t10k-images-idx3-ubyte.gz"
curl http://yann.lecun.com/exdb/mnist/t10k-labels-idx1-ubyte.gz --output "$1/t10k-labels-idx1-ubyte.gz"
gzip -d $1/*.gz