all:
	dune build src/main.exe && dune exec src/main.exe

doc:
	dune build @doc
