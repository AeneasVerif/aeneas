# The all target builds the project and runs it on a test file (whose path
# is currently hardcoded in main.ml). In order to check that we don't alter
# the behaviour of the interpreter while updating it, we check that the trace
# remains unchanged.
all:
	dune build src/main.exe && \
	dune exec src/main.exe > tests/trace_current.txt && \
	cmp tests/trace_reference.txt tests/trace_current.txt && \
	rm tests/trace_current.txt

doc:
	dune build @doc
