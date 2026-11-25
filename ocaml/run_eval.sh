#!/bin/bash

BUILD_DIR=_build/default/eval
BENCH_DIR=dttxt/samples

DATASETS=(digits.txt covtype.txt kddcup99.txt)

CMD="./$BUILD_DIR/main.exe ${DATASETS[@]/#/"$BENCH_DIR/"}"

echo $CMD
$CMD
