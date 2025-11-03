<<<<<<< HEAD
# SPI Protocol SystemVerilog Assertions (SVA)

此專案提供了一套完整的SPI(Serial Peripheral Interface)協議的SystemVerilog斷言(SVA)驗證套件。這些斷言可用於驗證SPI介面的正確性和完整性。

## 專案結構

```
.
├── README.md
├── rtl/
│   ├── spi_master_assertions.sv
│   ├── spi_slave_assertions.sv
│   └── spi_monitor_assertions.sv
└── doc/
    └── usage_guide.md
```

## 功能特點

此SVA套件分為三個主要組件：

### 1. SPI Master 斷言 (spi_master_assertions.sv)
- SCLK生成時序檢查
- CS控制時序驗證
- MOSI數據輸出時序監控
- 傳輸完整性檢查

### 2. SPI Slave 斷言 (spi_slave_assertions.sv)
- SCLK同步檢查
- CS響應時序驗證
- MISO數據輸出監控
- 數據接收正確性驗證

### 3. SPI Monitor 斷言 (spi_monitor_assertions.sv)
- 協議層面完整性監控
- 時鐘活動檢查
- 數據採樣驗證
- 位元組對齊檢查

## 使用方法

1. 將相應的斷言文件加入您的驗證環境中
2. 根據您的需求選擇使用master、slave或monitor斷言
3. 連接相應的信號到斷言模組

### 基本連接示例：

```systemverilog
// Master斷言連接示例
spi_master_assertions master_assert (
  .clk       (clk),
  .rst_n     (rst_n),
  .sclk      (sclk),
  .cs_n      (cs_n),
  .mosi      (mosi),
  .tx_data   (tx_data),
  .tx_valid  (tx_valid),
  .tx_ready  (tx_ready)
);
```

## 驗證環境要求

- SystemVerilog支援
- 支援SVA的模擬器
- UVM環境支援(可選)

## 授權

MIT License
=======
# SPI-SVA
>>>>>>> 26226e0e44d94231501b3f8047e165ffe395af09
