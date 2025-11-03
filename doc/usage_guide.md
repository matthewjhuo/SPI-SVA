# SPI SVA Usage Guide

本文檔提供了詳細的SPI SVA使用指南。

## 整合步驟

### 1. Master 斷言整合

```systemverilog
// 實例化master斷言
spi_master_assertions master_assert (
  .clk       (system_clk),
  .rst_n     (system_rst_n),
  .sclk      (spi_sclk),
  .cs_n      (spi_cs_n),
  .mosi      (spi_mosi),
  .tx_data   (master_tx_data),
  .tx_valid  (master_tx_valid),
  .tx_ready  (master_tx_ready)
);
```

### 2. Slave 斷言整合

```systemverilog
// 實例化slave斷言
spi_slave_assertions slave_assert (
  .clk       (system_clk),
  .rst_n     (system_rst_n),
  .sclk      (spi_sclk),
  .cs_n      (spi_cs_n),
  .miso      (spi_miso),
  .rx_data   (slave_rx_data),
  .rx_valid  (slave_rx_valid),
  .tx_data   (slave_tx_data),
  .tx_ready  (slave_tx_ready)
);
```

### 3. Monitor 斷言整合

```systemverilog
// 實例化monitor斷言
spi_monitor_assertions monitor_assert (
  .clk           (system_clk),
  .rst_n         (system_rst_n),
  .sclk          (spi_sclk),
  .cs_n          (spi_cs_n),
  .mosi          (spi_mosi),
  .miso          (spi_miso),
  .captured_mosi (monitor_mosi_data),
  .captured_miso (monitor_miso_data)
);
```

## 常見時序要求

1. SCLK相關時序
   - SCLK週期需符合協議規範
   - SCLK在CS非活動時必須保持穩定

2. CS相關時序
   - CS下降沿到第一個SCLK邊沿的建立時間
   - CS上升沿的保持時間
   - CS最小高電平時間

3. 數據相關時序
   - MOSI/MISO在SCLK採樣邊沿的建立和保持時間
   - 8位元資料傳輸對齊要求

## 驗證重點

1. 基本傳輸驗證
   - 完整的8位元傳輸
   - 正確的時序關係
   - 數據有效性

2. 特殊情況處理
   - 復位行為
   - 總線爭用情況
   - 錯誤恢復能力

3. 效能相關檢查
   - 最小傳輸間隔
   - 最大傳輸速率
   - 總線利用率

## 常見問題解決

1. 時序違規處理
   - 檢查時鐘配置
   - 驗證信號同步邏輯
   - 調整時序參數

2. 數據完整性問題
   - 確認位元順序
   - 檢查採樣點設置
   - 驗證數據對齊

3. 系統集成問題
   - 檢查接口連接
   - 驗證配置參數
   - 確認時鐘域
