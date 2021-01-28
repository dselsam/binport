PKG = Port34
include ./lean4/build/release/stage1/share/lean/lean.mk
all: port34

EXE=port34

port34: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(EXE)

$(BIN_OUT)/test: $(LIB_OUT)/libPort34.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`

.PHONY: clearLean3 clearMathlib buildLean3 buildMathlib unportLean3 unportMathlib portLean3 portMathlib portMathlibFast

AUTO4_PATH=./lib4/auto
LEAN3_PATH=./lean3/library:./lean3:leanpkg:./mathlib/src
LEAN4_PATH=./lean4/build/release/stage1/lib/lean:$(AUTO4_PATH)

clearLean3:
	find ./lean3/library -name "*olean" -delete
	find ./lean3/library -name "*tlean" -delete

clearMathlib:
	find ./mathlib/src -name "*olean" -delete
	find ./mathlib/src -name "*tlean" -delete

buildLean3:
	LEAN_PATH=$(LEAN3_PATH) time ./lean3/bin/lean --port ./lean3/library

buildMathlib:
	LEAN_PATH=$(LEAN3_PATH) time ./lean3/bin/lean --port ./mathlib/src

unportLean3:
	find $(AUTO4_PATH)/Lean3Lib -name "*.olean" -delete
	find $(AUTO4_PATH)/Lean3Lib -name "*.lean" -delete
	find $(AUTO4_PATH)/Lean3Pkg -name "*.olean" -delete
	find $(AUTO4_PATH)/Lean3Pkg -name "*.lean" -delete

unportMathlib:
	find $(AUTO4_PATH)/Mathlib -name "*.olean" -delete
	find $(AUTO4_PATH)/Mathlib -name "*.lean" -delete

portLean3:
	LEAN_PATH=$(LEAN4_PATH) time ./$(EXE) 1 lean3

portMathlib:
	LEAN_PATH=$(LEAN4_PATH) time ./$(EXE) 1 mathlib

portLean3Fast:
	LEAN_PATH=$(LEAN4_PATH) time ./$(EXE) 0 lean3

portMathlibFast:
	LEAN_PATH=$(LEAN4_PATH) time ./$(EXE) 0 mathlib
