PKG = BinPort
include $(LEAN4_S1_MK)
all: binport

BinPortEXE=binport

LIB4=./Lib4
LEAN3_PATH=$(LEAN3_LIB):$(LEAN3_PKG):$(MATHLIB_SRC)
LEAN4_PATH=$(LEAN4_S1_LIB):$(LIB4)

binport: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(BinPortEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libBinPort.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`

# TODO: make these packages
preport:
	LEAN_PATH=$(LEAN4_PATH) time lean --o=$(LIB4)/PrePort/Numbers.olean $(LIB4)/PrePort/Numbers.lean
	LEAN_PATH=$(LEAN4_PATH) time lean --o=$(LIB4)/PrePort.olean $(LIB4)/PrePort.lean

postport:
	LEAN_PATH=$(LEAN4_PATH) time lean --o=$(LIB4)/PostPort/Coe.olean $(LIB4)/PostPort/Coe.lean
	LEAN_PATH=$(LEAN4_PATH) time lean --o=$(LIB4)/PostPort/Pow.olean $(LIB4)/PostPort/Pow.lean
	LEAN_PATH=$(LEAN4_PATH) time lean --o=$(LIB4)/PostPort.olean $(LIB4)/PostPort.lean

portLean3: preport
	LEAN_PATH=$(LEAN4_PATH) time ./$(BinPortEXE) 1 lean3

portMathlib: preport
	LEAN_PATH=$(LEAN4_PATH) time ./$(BinPortEXE) 1 mathlib

portNullstellensatz: preport
	LEAN_PATH=$(LEAN4_PATH) time ./$(BinPortEXE) 1 nullstellensatz

portPrime: preport
	LEAN_PATH=$(LEAN4_PATH) time ./$(BinPortEXE) 1 prime
