PKG = Delaborate
include ../../lean4/build/release/stage1/share/lean/lean.mk
all: Delaborate

DelaborateEXE=delaborate

Delaborate: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(DelaborateEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libDelaborate.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`
