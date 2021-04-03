## Usage
```
$ omake
$ ./src/lambda-ma [<option>] <file0> <file1> ...
```

## Benchmarks
In a case that the number of functor applications is 10.
```
$ cd bench
$ sed -e 's/NUM_ITERATION/10/' fix_functor.mcod.ml > fix_functor.mcod.10.ml
$ ../src/lambda-ma fix_functor.mcod.10.ml > fix_functor.mcod.out.ml
$ make mcod
$ ./bench.out
```