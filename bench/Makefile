mcod: fix_functor.mcod.out.ml bench.ml print_code.ml
	metaocamlc -c fix_functor.mcod.out.ml -o fix_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc -c print_code.ml -o print_code
	metaocamlc fix_functor.cmo bench.cmo -o bench.out
	metaocamlc fix_functor.cmo print_code.cmo -o print_code.out

.PHONY: bench
bench:
	./bench.sh

clean:
	rm -f *.mli *.cmo *.cmi *.cmx *.a *.o *.out
