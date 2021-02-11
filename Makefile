PKG = MathPort
include ./lean4/build/release/stage1/share/lean/lean.mk
all: mathport

MathPortEXE=mathport
Lean4Exe=
LIB4=./Lib4
LEAN3_PATH=./lean3/library:./lean3/leanpkg:./mathlib/src
LEAN4_PATH=./lean4/build/release/stage1/lib/lean:$(LIB4)


mathport: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(MathPortEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libMathPort.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`


.PHONY: clearLean3 clearMathlib buildLean3 buildMathlib unportLean3 unportMathlib portLean3 portMathlib portMathlibFast

clearLean3:
	find ./lean3/library -name "*olean" -delete
	find ./lean3/library -name "*tlean" -delete

clearMathlib:
	find ./mathlib/src -name "*olean" -delete
	find ./mathlib/src -name "*tlean" -delete

buildLean3:
	LEAN_PATH=$(LEAN3_PATH) time ./lean3/bin/lean --make --tlean ./lean3/library
	LEAN_PATH=$(LEAN3_PATH) time ./lean3/bin/lean --make --tlean ./lean3/leanpkg

buildMathlib:
	LEAN_PATH=$(LEAN3_PATH) time ./lean3/bin/lean --make --tlean ./mathlib/src

unportLean3:
	rm -rf $(LIB4)/Lean3Lib $(LIB4)/Lean3Pkg

unportMathlib:
	rm -rf $(LIB4)/Mathlib

# TODO: simulate Lean3's `--make`
preport:
	LEAN_PATH=$(LEAN4_PATH) time ./lean4/build/release/stage1/bin/lean --o=$(LIB4)/PrePort/Number.olean $(LIB4)/PrePort/Number.lean
	LEAN_PATH=$(LEAN4_PATH) time ./lean4/build/release/stage1/bin/lean --o=$(LIB4)/PrePort.olean $(LIB4)/PrePort.lean

postport:
	LEAN_PATH=$(LEAN4_PATH) time ./lean4/build/release/stage1/bin/lean --o=$(LIB4)/PostPort/Coe.olean $(LIB4)/PostPort/Coe.lean
	LEAN_PATH=$(LEAN4_PATH) time ./lean4/build/release/stage1/bin/lean --o=$(LIB4)/PostPort.olean $(LIB4)/PostPort.lean

portLean3: preport
	LEAN_PATH=$(LEAN4_PATH) time ./$(MathPortEXE) 1 lean3

portMathlib: preport
	LEAN_PATH=$(LEAN4_PATH) time ./$(MathPortEXE) 1 mathlib

portLean3Fast:
	LEAN_PATH=$(LEAN4_PATH) time ./$(MathPortEXE) 0 lean3

portMathlibFast:
	LEAN_PATH=$(LEAN4_PATH) time ./$(MathPortEXE) 0 mathlib
