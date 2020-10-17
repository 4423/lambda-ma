mcod: fix_functor.mcod.ml fix_functor.mcod.opt.ml bench.ml
	metaocamlc -c fix_functor.mcod.ml -o fix_functor_mcod
	metaocamlc -c fix_functor.mcod.opt.ml -o fix_functor
	metaocamlc -c bench.ml -o bench
	metaocamlc fix_functor_mcod.cmo fix_functor.cmo bench.cmo -o bench.out

clean:
	rm -f *.mli *.cmo *.cmi *.cmx *.a *.o *.out
