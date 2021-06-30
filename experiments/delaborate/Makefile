PKG = Delaborate
include $(LEAN4_S1_MK)
all: delaborate

DelaborateEXE=delaborate
LEAN4_PATH=$(LEAN4_S1_LIB)

delaborate: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(DelaborateEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libDelaborate.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc --print-ldflags`
