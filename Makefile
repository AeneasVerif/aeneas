all:
	dune build src/main.exe && \
	dune exec src/main.exe > trace_current.txt && \
	cmp trace_reference.txt trace_current.txt

doc:
	dune build @doc
