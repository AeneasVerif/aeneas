all: build-run-check-trace

# Build the project and run the executable
.PHONY: build-run
build-run:
	dune build src/main.exe && dune exec src/main.exe

# Build the project and run the executable, then check that the behaviour
# of the interpreter didn't change by comparing the newly generated trace
# with a reference.
.PHONY: build-run-check-trace
build-run-check-trace:
	dune build src/main.exe && \
	dune exec src/main.exe ../charon/charon/tests/test1.cfim > tests/trace_current.txt && \
	cmp tests/trace_reference.txt tests/trace_current.txt && \
	rm tests/trace_current.txt

# Build the project and update the trace
.PHONY: regen-trace
regen-trace:
	dune build src/main.exe && \
	dune exec src/main.exe ../charon/charon/tests/test1.cfim > tests/trace_current.txt && \
        rm tests/trace_reference.txt && \
	mv tests/trace_current.txt tests/trace_reference.txt

doc:
	dune build @doc
