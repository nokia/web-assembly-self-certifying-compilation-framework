
OCB_SRC_FLAGS = \
  -I src/validator \
  -I src/validator/syntax \
  -I src/validator/utils \
  -I src/validator/proofs \
  -I src/validator/solver \
  -I src/validator/validator-api \
  -I src/validator/test \
  -I src/compiler/main \
  -I src/compiler/passes

OCB_PKG_FLAGS = -pkg wasm -pkg z3
# OCB_PKG_FLAGS = -package wasm -package z3

# Suppress "fields explicitly listed in record
OCB_WARN_FLAGS = -cflags '-w -23'
OCB_COMPILE_FLAGS = -tag 'debug' -tag 'thread'
OCB_FLAGS = -use-ocamlfind $(OCB_WARN_FLAGS) $(OCB_PKG_FLAGS) $(OCB_SRC_FLAGS) $(OCB_COMPILE_FLAGS)
OCB = ocamlbuild $(OCB_FLAGS)

all:
	$(OCB) whisk.byte
	$(OCB) whisk.native

tests:
	$(OCB) run_tests.byte
	$(OCB) run_tests.native

clean:
	$(OCB) -clean


