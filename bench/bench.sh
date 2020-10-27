#!/bin/sh

# prepare result file
RESULT_FILE=result.txt
echo -n '' > $RESULT_FILE
# 1. num of functor apllication
# 2. time for code generation [s]
# 3. time for runnning code [s]
# 4. memory usage [KB]

for i in `seq 0 100`
do
    OUT_FILE=fix_functor.mcod.out.ml
    # add measurement code
    echo 'let t1 = Sys.time () ;;' > $OUT_FILE
    # translate
    cat fix_functor.mcod.ml | sed s/NUM_ITERATION/$i/g | ../src/metamo >> $OUT_FILE
    # add measurement code
    echo ';;\nPrintf.printf "%f\\n" (Sys.time () -. t1);;' >> $OUT_FILE
    # compile translated code
    make mcod
    # run bench
    echo $i | tr '\n' '\t' >> $RESULT_FILE
    /usr/bin/time -f '%M' ./bench.out 2>&1 | tr '\n' '\t' >> $RESULT_FILE
    # clean
    make clean
    rm $OUT_FILE
done
