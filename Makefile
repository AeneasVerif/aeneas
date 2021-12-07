all:
	dune build src/main.exe && \
	dune exec src/main.exe > tests/trace_current.txt && \
	cmp tests/trace_reference.txt tests/trace_current.txt && \
	rm tests/trace_current.txt

doc:
	dune build @doc
