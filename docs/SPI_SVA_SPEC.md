## SPI SVA 規格（協定層）

本文件定義針對 SPI 協定的 SystemVerilog Assertions（SVA）需求與覆蓋範圍，支援 Mode 0~3（CPOL, CPHA 可參數化）、可配置資料位寬與位序，並聚焦於邏輯協定正確性而非電氣層。

### 目標
- 驗證在 `CS_n` 有效期間的 `SCLK/MOSI/MISO` 行為是否符合所選 CPOL/CPHA 模式之取樣/變化邊界。
- 檢查 `SCLK` 在 `CS_n` 為非有效（高電位）時必須閒置（不得切換）。
- 檢查 `CS_n` 低期間框定完整 frame，位元數量應等於 `DATA_WIDTH`。
- 檢查 `MOSI` 對取樣邊界的 setup/hold 時序（以時脈邊界級別，不涉實際延遲單位）。
- 檢查 `MISO` 在從裝置非選取時（`CS_n` 高）為高阻或不驅動（需由測試台或介面提供觀測鉤子）。
- 覆蓋不同 SPI 模式與位序、各種資料位寬。

### 參數與介面假設
- `CPOL` ∈ {0,1}：SCLK 閒置電平，0=低閒置、1=高閒置。
- `CPHA` ∈ {0,1}：資料取樣相位，0=第一沿取樣、1=第二沿取樣。
- `DATA_WIDTH`：傳輸位寬（預設 8，亦可 4/16/32 等）。
- `MSB_FIRST`：位序方向，1=MSB-first，0=LSB-first（用於覆蓋與一致性檢查，不強制資料內容）。
- `clk`/`reset_n`：系統觀測時脈/重設，作為斷言 clocking 基準。

### 規則（斷言）
1) SCLK 閒置規則
   - `CS_n` 為高（非選取）時，`SCLK` 必須維持在 CPOL 指定的閒置電平且不得切換。

2) CS 定義的 frame 邊界
   - 一個傳輸 frame 由 `CS_n` 下降緣開始，於 `CS_n` 上升緣結束。
   - `CS_n` 低期間不得出現不完整的半個 SCLK 週期（必須邊界完整）。
   - `CS_n` 低期間的有效取樣邊界計數應等於 `DATA_WIDTH`。

3) CPOL/CPHA 取樣與改變邊界
   - Mode 對應：
     - CPOL=0, CPHA=0（Mode 0）：取樣於上升沿，資料變化於下降沿。
     - CPOL=0, CPHA=1（Mode 1）：取樣於下降沿，資料變化於上升沿。
     - CPOL=1, CPHA=0（Mode 2）：取樣於下降沿，資料變化於上升沿（SCLK 閒置高）。
     - CPOL=1, CPHA=1（Mode 3）：取樣於上升沿，資料變化於下降沿（SCLK 閒置高）。

4) MOSI setup/hold（邏輯邊界級）
   - 在取樣沿的前一個對應「變化沿」後，取樣沿到來前，`MOSI` 應保持穩定。
   - 於取樣沿當下不可發生 `MOSI` 翻轉。

5) MISO 非選取行為
   - 在 `CS_n` 高期間，從裝置不應驅動 `MISO`（理想為 'z）。
   - 由於高阻難以直接斷言，此處提供可選觀測：
     - 以 tri-state 鉤子或 `miso_is_driven` 輔助訊號。

6) 位元數量一致性
   - 在一個 frame 內，取樣邊界次數 = `DATA_WIDTH`。
   - 若有 `MSB_FIRST` 設定，覆蓋項目需包含 MSB/LSB 方向的傳輸，協定本身不強制資料內容。

7) SCLK 高/低期間完整性
   - `CS_n` 低期間，SCLK 的高/低相各需至少 1 個系統時脈節拍（避免毛刺）。

### 覆蓋項目
- CPOL × CPHA 組合（4 個模式）切換至少各一次。
- `DATA_WIDTH` 覆蓋常見值（4, 8, 16）。
- `MSB_FIRST`/`LSB_FIRST` 各至少一次。
- CS 短包與長包（不同位寬）案例。

### 綁定與使用
- 以 `bind` 將 `spi_sva` 綁定至 DUT 或介面 `spi_if`。
- 由 `clk`/`reset_n` 作為 SVA clocking，在 `CS_n` 低期間追蹤 SCLK 邊界與 MOSI/MISO 穩定性。
- 可透過參數覆蓋不同模式與位寬。

### 限制與注意
- 未涵蓋真實電氣延遲，為純數位協定檢查。
- `MISO` 高阻行為需依測試平台實現（模擬器/介面模型）。
- SCLK 頻率上限/佔空比不在本版強制，僅做基本高低完整性檢查。


