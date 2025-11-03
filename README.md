## SPI-SVA

本專案提供 SPI 協定的 SystemVerilog Assertions 與簡單範例測試台，支援 CPOL/CPHA 模式（0~3）、可配置位寬與位序。

### 結構
- `docs/SPI_SVA_SPEC.md`：SVA 規格與覆蓋項目
- `sv/spi_if.sv`：SPI 介面（參數：`CPOL/CPHA/DATA_WIDTH/MSB_FIRST`）
- `sv/spi_sva.sv`：共用套件 `spi_sva_pkg`（函式/工具）
- `sv/sva/spi_master_sva.sv`：Master 專用 SVA
- `sv/sva/spi_slave_sva.sv`：Slave 專用 SVA
- `sv/sva/spi_monitor_sva.sv`：Monitor（被動監測）專用 SVA
- `sv/rtl/apb2spi.sv`：APB3 到 SPI 的主控 RTL（可直接驅動 `spi_if`）
- `sv/example/tb_spi.sv`：範例測試台（APB 寫入觸發 SPI 傳輸 + 簡單 slave stub）

### 使用方式
1) 將 `spi_if.sv`、`spi_sva.sv` 以及所需的 `sv/sva/*.sv` 與你的 DUT 一起編譯。
2) 在你的測試台建立 `spi_if` 實例並連接到 DUT 之 SPI 腳位。
3) 以 `bind` 或直接實例化下列模組（擇一或多個），並將 `spi_if` 傳入：

```systemverilog
spi_master_sva  #(.CPOL(0), .CPHA(0), .DATA_WIDTH(8), .MSB_FIRST(1)) u_spi_master (.sif(spi_if_inst));
spi_slave_sva   #(.CPOL(0), .CPHA(0), .DATA_WIDTH(8), .MSB_FIRST(1)) u_spi_slave  (.sif(spi_if_inst));
spi_monitor_sva #(.CPOL(0), .CPHA(0), .DATA_WIDTH(8), .MSB_FIRST(1)) u_spi_mon    (.sif(spi_if_inst));
```

### 模擬範例
可直接跑提供的測試台：

```sh
// 以你的模擬器為準（Questa/VCS/Xcelium 等），此為概念指引
vlog sv/spi_if.sv \
     sv/spi_sva.sv \
     sv/sva/spi_master_sva.sv sv/sva/spi_slave_sva.sv sv/sva/spi_monitor_sva.sv \
     sv/rtl/apb2spi.sv \
     sv/example/tb_spi.sv
vsim -c tb_spi -do "run -all; quit"
```

### 主要檢查項目
- `CS_n` 高時 `SCLK` 維持 CPOL 閒置電平且不得切換
- `CS_n` 低期間取樣邊界計數 = `DATA_WIDTH`
- CPOL/CPHA 所定義的取樣/變化邊界遵循
- 取樣沿當下 `MOSI` 穩定（不翻轉）
- `MOSI` 僅於變化沿切換（寬鬆警告）
- `MISO` 在未選取時不驅動（需 `miso_is_driven` 輔助訊號）

更多細節請見 `docs/SPI_SVA_SPEC.md`。


