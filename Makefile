# Makefile for SPI Protocol SVA Simulation

# 工具設定
VLOG = vlog
VSIM = vsim
VLOG_FLAGS = -sv
VSIM_FLAGS = -c -do "run -all; quit -f"

# 源文件
RTL_FILES = rtl/apb2spi.sv rtl/spi_master.sv
SVA_FILES = rtl/spi_master_assertions.sv rtl/spi_slave_assertions.sv rtl/spi_monitor_assertions.sv
TB_FILES = tb/apb2spi_tb.sv

# 目標文件
all: compile sim

# 編譯
compile:
	$(VLOG) $(VLOG_FLAGS) $(RTL_FILES) $(SVA_FILES) $(TB_FILES)

# 仿真
sim:
	$(VSIM) $(VSIM_FLAGS) apb2spi_tb

# 清理
clean:
	rm -rf transcript work vsim.wlf

# 查看波形
wave:
	$(VSIM) apb2spi_tb -do "do wave.do"

.PHONY: all compile sim clean wave
