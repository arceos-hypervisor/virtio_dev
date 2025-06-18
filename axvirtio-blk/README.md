# axvirtio-blk

VirtIO Block Device Backend Driver for ArceOS Hypervisor

## 项目概述

axvirtio-blk 是为 ArceOS 虚拟化平台设计的 VirtIO 块设备后端驱动，实现了 VirtIO 规范中的块设备协议，为虚拟机提供块存储服务。

## 架构设计

```
axvirtio-blk/
├── src/
│   ├── lib.rs              # 库入口，导出公共接口
│   ├── block.rs            # 主设备结构体和 MMIO 接口实现
│   ├── devops_impl.rs      # BaseDeviceOps trait 实现
│   ├── protocol/           # VirtIO-BLK 协议相关
│   │   ├── mod.rs          # 协议模块导出
│   │   ├── constants.rs    # 协议常量定义
│   │   ├── structures.rs   # 请求/响应结构体
│   │   └── error.rs        # 错误类型定义
│   ├── backend/            # 存储后端抽象
│   │   ├── mod.rs          # 后端模块导出
│   │   ├── traits.rs       # BlockBackend trait 定义
│   │   └── memory.rs       # 内存存储后端实现
│   └── queue/              # 队列处理逻辑
│       ├── mod.rs          # 队列模块导出
│       ├── parser.rs       # 描述符链解析
│       └── processor.rs    # 请求处理执行
```

## 已实现功能

### ✅ VirtIO MMIO 接口

- **完整的 MMIO 寄存器支持**：实现了标准 VirtIO MMIO 规范中的所有寄存器

  - 设备识别寄存器 (MAGIC_VALUE, VERSION, DEVICE_ID, VENDOR_ID)
  - 特性协商寄存器 (DEVICE_FEATURES, DRIVER_FEATURES)
  - 队列配置寄存器 (QUEUE_SEL, QUEUE_NUM, QUEUE_READY, etc.)
  - 状态和中断寄存器 (STATUS, INTERRUPT_STATUS, INTERRUPT_ACK)
  - 配置空间访问

- **设备状态管理**：完整的设备初始化状态机
  - RESET → ACKNOWLEDGE → DRIVER → FEATURES_OK → DRIVER_OK
  - 错误状态处理和恢复

### ✅ VirtIO-BLK 协议实现

- **标准请求类型支持**：
  - `VIRTIO_BLK_T_IN` (读请求)
  - `VIRTIO_BLK_T_OUT` (写请求)
  - `VIRTIO_BLK_T_FLUSH` (刷新请求)
- **请求结构体解析**：

  - `virtio_blk_outhdr` 请求头解析
  - 数据缓冲区处理
  - 状态字节返回

- **响应状态码**：
  - `VIRTIO_BLK_S_OK` (成功)
  - `VIRTIO_BLK_S_IOERR` (I/O 错误)
  - `VIRTIO_BLK_S_UNSUPP` (不支持的操作)

### ✅ 队列处理机制

- **描述符链解析**：完整实现描述符链遍历和解析

  - 支持多描述符链式请求
  - 正确处理 VIRTQ_DESC_F_NEXT 和 VIRTQ_DESC_F_WRITE 标志
  - 验证描述符链完整性

- **可用环和已用环处理**：
  - 从可用环读取新请求
  - 向已用环写入完成的请求
  - 支持中断抑制机制

### ✅ 存储后端抽象

- **BlockBackend Trait**：定义了统一的存储后端接口

  - `read()` - 读取数据
  - `write()` - 写入数据
  - `flush()` - 刷新缓存
  - `capacity()` - 获取容量
  - `is_read_only()` - 只读检查

- **内存存储后端**：实现了基于内存的存储后端

  - 支持读写操作
  - 支持只读模式
  - 扇区对齐访问验证

- **文件存储后端** (feature: `file-backend`)：实现了基于文件的持久化存储后端
  - 支持持久化存储 (虚拟机重启后数据保留)
  - 基于 ArceOS 文件系统 API (`axfs`)
  - 支持多种文件系统格式 (FAT32, RAM filesystem 等)
  - 扇区到字节的地址转换
  - 完整的文件权限和错误处理

### ✅ 特性支持

- **基础特性**：
  - `VIRTIO_F_RING_EVENT_IDX` (事件索引)
  - `VIRTIO_BLK_F_FLUSH` (刷新支持)
- **设备配置**：
  - 容量信息报告
  - 扇区大小配置 (512 字节)

### ✅ 错误处理

- **完整的错误类型定义**：覆盖所有可能的错误情况
- **错误到状态码映射**：将内部错误正确转换为 VirtIO 状态码
- **错误恢复机制**：在错误情况下正确更新队列状态

## 临时解决方案 / 未完善功能

### ⚠️ 地址转换机制

**当前状态**：使用简化的地址转换逻辑

- 直接使用客户机物理地址作为主机虚拟地址
- 缺少完整的客户机物理地址到主机虚拟地址的映射验证
- 可能存在地址访问安全性问题

**计划改进**：

- 集成完整的地址空间管理
- 添加地址映射验证
- 实现安全的内存访问检查

### ⚠️ 高级特性支持

**当前缺失**：

- `VIRTIO_BLK_F_SIZE_MAX` (最大段大小)
- `VIRTIO_BLK_F_SEG_MAX` (最大段数量)
- `VIRTIO_BLK_F_GEOMETRY` (磁盘几何信息)
- `VIRTIO_BLK_F_RO` (只读设备)
- `VIRTIO_BLK_F_MQ` (多队列支持)
- `VIRTIO_BLK_F_DISCARD` (丢弃操作)
- `VIRTIO_BLK_F_WRITE_ZEROES` (写零操作)

### ⚠️ 存储后端限制

**当前状态**：支持内存和文件存储后端

- ✅ 内存存储后端 (已实现)
- ✅ 文件存储后端 (已实现，需启用 `file-backend` 特性)
- ❌ 缺少网络存储后端
- ❌ 缺少高级配置选项

**计划扩展**：

- 网络块设备后端
- 动态容量调整
- 高级缓存策略

### ⚠️ 性能优化

**当前限制**：

- 未实现零拷贝优化
- 缺少批量请求处理
- 单队列限制 (未支持多队列)

### ⚠️ 调试和监控

**当前状态**：基础日志记录

- 缺少详细的性能指标
- 缺少请求追踪机制
- 缺少错误统计

## 使用示例

```rust
use axvirtio_blk::Block;

// 创建内存块设备实例
let block_device = Block::new(
    0,                    // 设备ID
    1024 * 1024 * 1024,  // 1GB容量
    0x1000_0000,         // 内存偏移
);

// 使用文件存储后端 (需启用 file-backend 特性)
#[cfg(feature = "file-backend")]
{
    use axvirtio_blk::backend::FileBackend;

    // 创建新文件作为存储后端
    let file_backend = FileBackend::new(
        "/path/to/storage.img",    // 文件路径
        1024 * 1024 * 1024,        // 1GB容量
        false,                     // 可读写
    ).expect("Failed to create file backend");

    // 打开现有文件作为存储后端
    let existing_backend = FileBackend::open_existing(
        "/path/to/existing.img",   // 现有文件路径
        true,                      // 只读模式
    ).expect("Failed to open file backend");
}

// 设备会自动处理来自虚拟机的MMIO访问
// 通过 BaseDeviceOps trait 集成到设备管理系统中
```

## 依赖项

- `axdevice_base` - 设备基础抽象
- `axaddrspace` - 地址空间管理
- `axfs` - ArceOS 文件系统 (可选，需启用 `file-backend` 特性)
- `virtio-bindings` - VirtIO 协议绑定
- `log` - 日志记录
- `spin` - 自旋锁
- `axerrno` - 错误码定义

## 兼容性

- **VirtIO 版本**：支持 VirtIO 1.0+ 规范
- **传输层**：MMIO 传输 (PCI 传输暂未支持)
- **客户机支持**：Linux virtio-blk 驱动完全兼容

## 开发状态

当前版本提供了完整的基础功能，足以支持虚拟机的基本块设备需求。主要的临时解决方案集中在地址转换和高级特性支持上，这些不影响基本的读写操作功能。

## 未来规划

1. **完善地址转换机制**
2. **实现文件存储后端**
3. **添加高级 VirtIO 特性支持**
4. **性能优化和多队列支持**
5. **添加详细的监控和调试功能**
