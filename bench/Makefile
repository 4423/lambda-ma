mcod: fix_functor.mcod.out.ml bench.ml
	metaocamlc -c fix_functor.mcod.out.ml -o fix_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc fix_functor.cmo bench.cmo -o bench.out

.PHONY: bench
bench:
	./bench.sh

clean:
	rm -f *.mli *.cmo *.cmi *.cmx *.a *.o *.out
