#!/bin/sh

# prepare result file
RESULT_FILE=result.txt
rm $RESULT_FILE
echo -n '' > $RESULT_FILE
# 1. num of functor apllication
# 2. time for code generation [s]
# 3. time for runnning code [s]
# 4. memory usage [KB]

filesize () {
    size=$(wc -c < $1)
    echo $size '1000.0' | awk '{printf "%f", $1 / $2}'
}

for i in `seq 0 1`
do
    OUT_FILE=fix_functor.mcod.out.ml
    # add measurement code
    echo 'let t1 = Sys.time () ;;' > $OUT_FILE
    # translate
    OUT_TMP_FILE=fix_functor.mcod.out.tmp.ml
    cat fix_functor.mcod.ml | sed s/NUM_ITERATION/$i/g > $OUT_TMP_FILE
    ../src/lambda-ma $OUT_TMP_FILE >> $OUT_FILE
    rm $OUT_TMP_FILE
    # add measurement code
    echo ';;\nPrintf.printf "%f\\n" (Sys.time () -. t1);;' >> $OUT_FILE
    # compile translated code
    make mcod
    # run bench
    echo $i | tr '\n' '\t' >> $RESULT_FILE
    /usr/bin/time -f '%M' ./bench.out 2>&1 | tr '\n' '\t' >> $RESULT_FILE
    # measure size of code
    ./print_code.out | sed -e '1d' > code.dump
    filesize code.dump >> $RESULT_FILE
    rm code.dump
    echo '' >> $RESULT_FILE
    # clean
    make clean
    rm $OUT_FILE
done
