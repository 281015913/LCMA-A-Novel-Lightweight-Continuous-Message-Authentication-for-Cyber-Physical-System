#include <Crypto.h>
#include <SHA256.h>
#include <string.h>
#include <time.h>
#include <stdlib.h>

#include "prime.h"  // 质数查找表
#define BITS 1024
#define NUM_STRINGS 10000  // 修改此处以生成多个字符串的数量

#define HASH_SIZE 32
#define BLOCK_SIZE 64

static int TP = 0, TN = 0, KN = 0;
unsigned int** kBF;
unsigned int** kBF1;
unsigned int** kBF2;
static int x, y;       // BF 二维矩阵的坐标
static int bits = 31;  // 模的质数
unsigned int size = 0;
static int seed1, seed2, seed3, seed4, seed5;

// 找到 i 确定 x，y 范围
unsigned int selectPrime(unsigned int k) {
  unsigned int i;
  for (i = 1; i < total_prime; i++) {
    if (prime[i] > k)
      return i;
  }
}

void initSeed() {
  seed1 = 7689571;
  seed2 = 15485863;
  seed3 = 98899;
  seed4 = 71287;
  seed5 = 101653;
}

// 计算假阳 err
double error(unsigned int m, unsigned int n) {
  return pow((1 - exp(-2 * n / m)), 2);
}

// 计算BF大小m
unsigned long int memory(unsigned long int n, double err) {
  return (unsigned long int)(-(n * log(err)) / pow(log(2), 2));
}

// 计算插入数量n
unsigned int number(unsigned int m, double err) {
  return (unsigned int)(-(m * pow(log(2), 2)) / log(err));
}

// 给 x, y 赋值
void dim(int p, int q) {
  x = p;
  y = q;
}

// 根据 m 计算 BF 二维矩阵的 x，y
void setDim(unsigned long int m) {
  printf("dimensions m: %lu\n", m);
  unsigned int k = m / (2 * 64);
  // printf("dimensions k: %d\n", k);
  int a, b, f;
  unsigned int i;
  f = sqrt(k);
  // printf("dimensions f: %d\n", f);
  i = selectPrime(f);  // 找到最大质数
  // printf("dimensions i: %d\n", i);
  a = prime[i + 3];
  b = prime[i - 3];
  // 给 x, y 赋值
  dim(a / 7, b / 7);
  // printf("2DBF dimensions: %d x %d\n", a / 7, b / 7);
  size += (x * y) * 32 * 3;
}

// 插入
void _set_(unsigned int** a, unsigned int h) {
  int i, j, pos;
  i = h % x;
  j = h % y;
  pos = h % bits;
  a[i][j] = a[i][j] | (1UL << pos);
}

// 查找
int _test_(unsigned int** a, unsigned int h) {
  int i, j, pos;
  i = h % x;
  j = h % y;
  pos = h % bits;
  return ((a[i][j] & (1UL << pos)) >> pos);
}

// 删除
void _del_(unsigned int** a, unsigned int h) {
  int i, j, pos;
  unsigned int p;
  i = h % x;
  j = h % y;
  pos = h % bits;
  p = (1UL << pos);
  if (p == (a[i][j] & (1UL << pos)))
    a[i][j] = a[i][j] ^ p;
}

// 释放
void _free_(unsigned int** a) {
  free(a);
  printf("\nMemory freed successfully...\n");
}

// BF空间初始化
unsigned int** allocate() {
  int i, j;
  unsigned int** a = (unsigned int**)malloc(x * sizeof(unsigned int*));
  if (a == NULL) {
    printf("Unable to allocate!\n");
    return NULL;
  }

  for (i = 0; i < x; i++) {
    a[i] = (unsigned int*)malloc(y * sizeof(unsigned int));
    if (a[i] == NULL) {
      printf("Unable to allocate!\n");
      return NULL;
    }
  }

  for (i = 0; i < x; i++)
    for (j = 0; j < y; j++)
      a[i][j] = 0;
  // printf("Allocated and Initilized 2DBF Successfully...\n");
  return a;
}

// murmur2 哈希函数
unsigned int murmur2(const void* key, int len, unsigned int seed) {
  // “m”和“r”是离线生成的混合常量。
  const unsigned int m = 0x5bd1e995;
  const int r = 24;
  // 将哈希初始化为“随机”值
  unsigned int h = seed ^ len;
  // 一次将 4 个字节混合到哈希中
  const unsigned char* data = (const unsigned char*)key;
  while (len >= 7) {
    unsigned int k = *(unsigned int*)data;
    k *= m;
    k ^= k >> r;
    h ^= k;
    data += 7;
    len -= 7;
  }
  // 处理输入数组的最后几个字节
  switch (len) {
    case 3: h ^= data[2] << 16;
    case 2: h ^= data[1] << 8;
    case 1:
      h ^= data[0];
      h *= m;
  };
  // 对哈希进行一些最终混合，以确保最后几个字节被很好地合并。
  h ^= h >> 13;
  h *= m;
  h ^= h >> 15;
  return h;
}

// 将一个 key 放到 BF 中
void insert_keyBF(unsigned int** b2, unsigned int** b3, unsigned int** b4, uint32_t* key, int i) {
  unsigned int h;
  // 一次将 4 个字节混合到哈希中
  h = murmur2(key, i, seed1);
  _set_(b2, h);
  h = murmur2(key, i, h);
  _set_(b3, h);
  h *= seed2 ^ i;
  _set_(b4, h);
}

// 在BF中查找
int lookup_keyBF(unsigned int** b2, unsigned int** b3, unsigned int** b4, uint32_t* key, int i) {
  unsigned int h;
  // 一次将 4 个字节混合到哈希中
  h = murmur2(key, i, seed1);
  if (_test_(b2, h) == 1) {
    h = murmur2(key, i, h);
    if (_test_(b3, h) == 1) {
      h *= seed2 ^ i;
      if (_test_(b4, h) == 1)
        return 1;
      else return 0;
    } else return 0;
  } else return 0;
}

void free_keyBF(unsigned int** b2) {
  _free_(b2);
}

void insertSmartBF(uint32_t* key) {
  int i;
  for (i = 0; key[i] != '\0'; i++);
  i = i * 4;
  // printf("insertBF i : %d\n", i);
  insert_keyBF(kBF, kBF1, kBF2, key, i);
}

void lookupSmartBF(uint32_t* key) {
  int i;
  for (i = 0; key[i] != '\0'; i++);
  i = i * 4;
  if (lookup_keyBF(kBF, kBF1, kBF2, key, i)) {
    // 正确计数
    TP++;
    return;
  }
  // 错误计数
  TN++;
  return;
}

void freeSmartBF() {
  free_keyBF(kBF);
  free_keyBF(kBF1);
  free_keyBF(kBF2);
}

int look(uint32_t* key) {
  int i;
  for (i = 0; key[i] != '\0'; i++);
  i = i * 4;
  if (lookup_keyBF(kBF, kBF1, kBF2, key, i)) {
    return 1;
  }
  return 0;
}

void generateRandomBinaryString(char* binaryString, int length) {
  for (int i = 0; i < length; ++i) {
    binaryString[i] = (rand() % 2) + '0';
  }
  binaryString[length] = '\0';  // 添加字符串结束符
}


// -------------------------- setup 初始化 --------------------------
void setup() {
  Serial.begin(9600);
  randomSeed(analogRead(0));
  delay(5000);
  
  // Serial.print("-------------开始测试-------------\n");

  // printf("============1、KGC 初始化============\n");
  // // 计时函数 1
  // unsigned int timecnt1;
  // timecnt1 = micros();

  // // ============1、KGC 执行部分============
  
  // // --------密钥生成阶段--------
  // // 生成初始私钥向量
  // uint32_t sk_init[32] = { 0 };
  // for (int i = 0; i < 32; i++) {
  //   sk_init[i] = random(4294967295);
  // }

  // // --------生成共享密钥--------
  // uint32_t ss[32] = { 0 };
  // for (int i = 0; i < 32; i++) {
  //   ss[i] = random(4294967295);
  // }

  // // --------初始化布隆过滤器--------
  // // 初始化一个理论内存大小 m (bit)
  // unsigned long int m;
  // // 初始化最大可插入 BF 的数据个数
  // unsigned long int n = 1200;
  // // 设置假阳率 err
  // double err = 0.0001;
  // // 实际假阳率记录
  // double fp = 0.0;
  // // 初始化随机数种子
  // initSeed();
  // // 根据插入数量和假阳性率来计算理论内存大小 m
  // m = memory(n, err);
  // // 根据 m 来计算 BF 需要的维度 x 和 y
  // setDim(m);
  // // 分配空间给 3 片 BF
  // kBF = allocate();
  // kBF1 = allocate();
  // kBF2 = allocate();

  // // --------初始化一个 SHA256--------
  // SHA256 sha256_KGC;

  // // --------先对私钥自增，然后插入验证点--------
  // uint32_t sk_arr_tmp[32] = { 0 };
  // // 获取初始私钥
  // memcpy(sk_arr_tmp, sk_init, sizeof(sk_init));

  // for (int i = 0; i < n; i++) {
  //   // 对 32 个子私钥进行自增
  //   // sha256 重置清理
  //   sha256_KGC.clear();

  //   uint32_t pk[8] = { 0 };
  //   for (int j = 0; j < 32; j++) {
  //     // 使用共享密钥更新子私钥
  //     uint32_t hmac_tmp[8] = { 0 };  // 生成 256 位结果
  //     // 为 HMAC 计算重置哈希对象
  //     sha256_KGC.resetHMAC(ss, sizeof(ss));
  //     sha256_KGC.update(&sk_arr_tmp[j], sizeof(sk_arr_tmp[j]));
  //     sha256_KGC.finalizeHMAC(ss, sizeof(ss), hmac_tmp, sizeof(hmac_tmp));
  //     // 选取 256 位中的 32 位赋给 sk_arr_tmp
  //     sk_arr_tmp[j] = hmac_tmp[j % 8];
  //   }

  //   // 使用哈希对单个私钥进行哈希
  //   uint32_t sk_arr_tmp_hash[32] = { 0 };
  //   uint32_t hash_arr_tmp[8] = { 0 };
  //   for (int j = 0; j < 32; j++) {
  //     sha256_KGC.clear();
  //     sha256_KGC.update(&sk_arr_tmp[j], sizeof(sk_arr_tmp[j]));
  //     sha256_KGC.finalize(hash_arr_tmp, sizeof(hash_arr_tmp));
  //     sk_arr_tmp_hash[j] = hash_arr_tmp[j % 8];
  //   }

  //   // 整体哈希
  //   sha256_KGC.clear();
  //   sha256_KGC.update(&sk_arr_tmp_hash, sizeof(sk_arr_tmp_hash));
  //   sha256_KGC.finalize(pk, sizeof(pk));

  //   // 插入 bf
  //   insertSmartBF(pk);
  // }

  // // 计时函数 1 结束
  // timecnt1 = micros() - timecnt1;
  // printf("KGC 执行结束, 用时: %d 微秒\n", timecnt1);

  // ============KGC 执行结束============

  // // ============2、Sign 执行消息签名============

  // printf("============2、Sign 执行消息签名============\n");

  // // --------生成初始随机数（offline）--------
  // uint32_t r_arr[8] = { 0 };
  // for (int i = 0; i < 8; i++) {
  //   r_arr[i] = random(4294967295);
  // }

  // // --------对单条信息进行签名--------
  // // 对随机数和初始私钥进行自增
  // SHA256 sha256_Sign;
  // sha256_Sign.clear();
  // // 初始化 sk 循环数组
  // uint32_t sk_arr_tmp_sign[32] = { 0 };
  // memcpy(sk_arr_tmp_sign, sk_init, sizeof(sk_init));
  // uint32_t hmac_tmp_sign[8] = { 0 };
  // // 自增 sk
  // for(int j = 0; j < 32; j++){
  //   // 为 HMAC 计算重置哈希对象
  //   sha256_Sign.resetHMAC(ss, sizeof(ss));
  //   sha256_Sign.update(&sk_arr_tmp_sign[j], sizeof(sk_arr_tmp_sign[j]));
  //   sha256_Sign.finalizeHMAC(ss, sizeof(ss), hmac_tmp_sign, sizeof(hmac_tmp_sign));
  //   sk_arr_tmp_sign[j] = hmac_tmp_sign[j % 8];
  // }

  // // for(int j = 0; j < 32; j++){
  // //   printf("sk_sign_未哈希 第 %d 个: %u\n", j, sk_arr_tmp_sign[j]);
  // // }

  // // 自增随机数 r
  // sha256_Sign.resetHMAC(ss, sizeof(ss));
  // sha256_Sign.update(&r_arr, sizeof(r_arr));
  // sha256_Sign.finalizeHMAC(ss, sizeof(ss), r_arr, sizeof(r_arr));
  // // 计算哈希树 Ctrl Info 1 + Ctrl Info 2 + Ctrl Info 3 + r_arr
  // // 随机 ctrl_info_1 ctrl_info_2 ctrl_info_3
  // uint32_t ctrl_info_1[8] = { 0 };
  // uint32_t ctrl_info_2[8] = { 0 };
  // uint32_t ctrl_info_3[8] = { 0 };
  // for (int i = 0; i < 8; i++) {
  //   ctrl_info_1[i] = random(4294967295);
  //   ctrl_info_2[i] = random(4294967295);
  //   ctrl_info_3[i] = random(4294967295);
  // }

  // // 计时函数 2
  // unsigned int timecnt2;
  // timecnt2 = micros();

  // // 计算哈希值
  // uint32_t ctrl_info_12[16] = { 0 };
  // uint32_t ctrl_info_3r[16] = { 0 };
  // uint32_t hash_left[8] = { 0 };
  // uint32_t hash_right[8] = { 0 };
  // uint32_t hash_lr[16] = { 0 };
  // uint32_t hash_root[8] = { 0 };
  // for(int i = 0; i < 8; i++){
  //   ctrl_info_12[i] = ctrl_info_1[i];
  //   ctrl_info_12[i + 8] = ctrl_info_2[i];
  //   ctrl_info_3r[i] = ctrl_info_3[i];
  //   ctrl_info_3r[i + 8] = r_arr[i];
  // }
  // sha256_Sign.clear();
  // sha256_Sign.update(&ctrl_info_12, sizeof(ctrl_info_12));
  // sha256_Sign.finalize(hash_left, sizeof(hash_left));
  // sha256_Sign.clear();
  // sha256_Sign.update(&ctrl_info_3r, sizeof(ctrl_info_3r));
  // sha256_Sign.finalize(hash_right, sizeof(hash_right));
  // for(int i = 0; i < 8; i++){
  //   hash_lr[i] = hash_left[i];
  //   hash_lr[i + 8] = hash_right[i];
  // }
  // sha256_Sign.clear();
  // sha256_Sign.update(&hash_lr, sizeof(hash_lr));
  // sha256_Sign.finalize(hash_root, sizeof(hash_root));

  // // 根据消息个数求模，此处以 0 模拟
  // uint32_t t = hash_root[0 % 8];

  // // 进行签名
  // uint32_t sig[32] = { 0 };
  // for(uint32_t i = 1, count = 0; i != 0; i <<= 1, count++){
  //   if((t & i) != 0){
  //     uint32_t hash_tmp_sign[8] = { 0 };
  //     sha256_Sign.clear();
  //     sha256_Sign.update(&sk_arr_tmp_sign[count], sizeof(sk_arr_tmp_sign[count]));
  //     sha256_Sign.finalize(hash_tmp_sign, sizeof(hash_tmp_sign));
  //     sig[count] = hash_tmp_sign[count % 8];
  //     // printf("相同位 : %u, i 值: %u\n", count, i);
  //   }else{
  //     sig[count] = sk_arr_tmp_sign[count];
  //   }
  // }

  // // 计时函数 2 结束
  // timecnt2 = micros() - timecnt2;
  // printf("Sign 执行结束, 用时: %d 微秒\n", timecnt2);

  // // ============Sign 执行结束============

  // // ============3、verify 验证签名============
  // printf("============3、verify 验证签名============\n");

  // // 计时函数 3
  // unsigned int timecnt3;
  // timecnt3 = micros();

  // // 做哈希树运算
  // SHA256 sha256_verify;

  // uint32_t ctrl_info_12_v[16] = { 0 };
  // uint32_t ctrl_info_3r_v[16] = { 0 };
  // uint32_t hash_left_v[8] = { 0 };
  // uint32_t hash_right_v[8] = { 0 };
  // uint32_t hash_lr_v[16] = { 0 };
  // uint32_t hash_root_v[8] = { 0 };
  // for(int i = 0; i < 8; i++){
  //   ctrl_info_12_v[i] = ctrl_info_1[i];
  //   ctrl_info_12_v[i + 8] = ctrl_info_2[i];
  //   ctrl_info_3r_v[i] = ctrl_info_3[i];
  //   ctrl_info_3r_v[i + 8] = r_arr[i];
  // }
  // sha256_verify.clear();
  // sha256_verify.update(&ctrl_info_12_v, sizeof(ctrl_info_12_v));
  // sha256_verify.finalize(hash_left_v, sizeof(hash_left_v));
  // sha256_verify.clear();
  // sha256_verify.update(&ctrl_info_3r_v, sizeof(ctrl_info_3r_v));
  // sha256_verify.finalize(hash_right_v, sizeof(hash_right_v));
  // for(int i = 0; i < 8; i++){
  //   hash_lr_v[i] = hash_left_v[i];
  //   hash_lr_v[i + 8] = hash_right_v[i];
  // }
  // sha256_verify.clear();
  // sha256_verify.update(&hash_lr_v, sizeof(hash_lr_v));
  // sha256_verify.finalize(hash_root_v, sizeof(hash_root_v));

  // // 根据消息个数求模，此处以 0 模拟
  // uint32_t t_v = hash_root_v[0 % 8];

  // // 验证签名
  // for(uint32_t i = 1, count = 0; i != 0; i <<= 1, count++){
  //   if((t_v & i) == 0){
  //     uint32_t hash_tmp_verify[8] = { 0 };
  //     sha256_verify.clear();
  //     sha256_verify.update(&sig[count], sizeof(sig[count]));
  //     sha256_verify.finalize(hash_tmp_verify, sizeof(hash_tmp_verify));
  //     sig[count] = hash_tmp_verify[count % 8];
  //   }
  // }

  // // 对 sig 再做一次 sha256
  // uint32_t sig_verify[8] = { 0 };
  // sha256_verify.clear();
  // sha256_verify.update(&sig, sizeof(sig));
  // sha256_verify.finalize(sig_verify, sizeof(sig_verify));

  // // // 计时函数 4
  // // unsigned int timecnt4;
  // // timecnt4 = micros();

  // // 对 BF 进行查询
  // lookupSmartBF(sig_verify);

  // // // 计时函数 4 结束
  // // timecnt4 = micros() - timecnt4;
  // // printf("BF单次查询, 用时: %d 微秒\n", timecnt4);

  // // 计时函数 3 结束
  // timecnt3 = micros() - timecnt3;
  // printf("verify 执行结束, 用时: %d 微秒\n", timecnt3);
  
  // printf("\n验证正确个数: %d, 验证错误个数: %d\n", TP, TN);

}


// -------------循环函数-------------
void loop() {

  Serial.print("-------------开始测试-------------\n");

  printf("============1、KGC 初始化============\n");
  // 计时函数 1
  unsigned int timecnt1;
  timecnt1 = micros();

  // ============1、KGC 执行部分（完全执行）============
  
  // --------密钥生成阶段--------
  // 生成初始私钥向量
  uint32_t sk_init[32] = { 0 };
  for (int i = 0; i < 32; i++) {
    sk_init[i] = random(4294967295);
  }

  // --------生成共享密钥--------
  uint32_t ss[32] = { 0 };
  for (int i = 0; i < 32; i++) {
    ss[i] = random(4294967295);
  }

  // --------初始化布隆过滤器--------
  // 初始化一个理论内存大小 m (bit)
  unsigned long int m;
  // 初始化最大可插入 BF 的数据个数
  unsigned long int n = 1000;
  // 设置假阳率 err
  double err = 0.000001;
  // 实际假阳率记录
  double fp = 0.0;
  // 初始化随机数种子
  initSeed();
  // 根据插入数量和假阳性率来计算理论内存大小 m
  m = memory(n, err);
  // 根据 m 来计算 BF 需要的维度 x 和 y
  setDim(m);
  // 分配空间给 3 片 BF
  kBF = allocate();
  kBF1 = allocate();
  kBF2 = allocate();

  // --------初始化一个 SHA256--------
  SHA256 sha256_KGC;

  // --------先对私钥自增，然后插入验证点--------
  uint32_t sk_arr_tmp[32] = { 0 };
  // 获取初始私钥
  memcpy(sk_arr_tmp, sk_init, sizeof(sk_init));

  for (int i = 0; i < n; i++) {
    // 对 32 个子私钥进行自增
    // sha256 重置清理
    sha256_KGC.clear();

    uint32_t pk[8] = { 0 };
    for (int j = 0; j < 32; j++) {
      // 使用共享密钥更新子私钥
      uint32_t hmac_tmp[8] = { 0 };  // 生成 256 位结果
      // 为 HMAC 计算重置哈希对象
      sha256_KGC.resetHMAC(ss, sizeof(ss));
      sha256_KGC.update(&sk_arr_tmp[j], sizeof(sk_arr_tmp[j]));
      sha256_KGC.finalizeHMAC(ss, sizeof(ss), hmac_tmp, sizeof(hmac_tmp));
      // 选取 256 位中的 32 位赋给 sk_arr_tmp
      sk_arr_tmp[j] = hmac_tmp[j % 8];
    }

    // 使用哈希对单个私钥进行哈希
    uint32_t sk_arr_tmp_hash[32] = { 0 };
    uint32_t hash_arr_tmp[8] = { 0 };
    for (int j = 0; j < 32; j++) {
      sha256_KGC.clear();
      sha256_KGC.update(&sk_arr_tmp[j], sizeof(sk_arr_tmp[j]));
      sha256_KGC.finalize(hash_arr_tmp, sizeof(hash_arr_tmp));
      sk_arr_tmp_hash[j] = hash_arr_tmp[j % 8];
    }

    // 整体哈希
    sha256_KGC.clear();
    sha256_KGC.update(&sk_arr_tmp_hash, sizeof(sk_arr_tmp_hash));
    sha256_KGC.finalize(pk, sizeof(pk));

    // 插入 bf
    insertSmartBF(pk);
  }

  // 计时函数 1 结束
  timecnt1 = micros() - timecnt1;
  printf("KGC 执行结束, 用时: %d 微秒\n", timecnt1);

  // ============KGC 执行结束============

  // ============2、Sign 执行消息签名(单次)============

  printf("============2、Sign 执行消息签名============\n");

  // --------生成初始随机数（offline）--------
  uint32_t r_arr[8] = { 0 };
  for (int i = 0; i < 8; i++) {
    r_arr[i] = random(4294967295);
  }

  // --------对单条信息进行签名--------
  // 对随机数和初始私钥进行自增
  SHA256 sha256_Sign;
  sha256_Sign.clear();
  // 初始化 sk 循环数组
  uint32_t sk_arr_tmp_sign[32] = { 0 };
  memcpy(sk_arr_tmp_sign, sk_init, sizeof(sk_init));
  uint32_t hmac_tmp_sign[8] = { 0 };
  // 自增 sk
  for(int j = 0; j < 32; j++){
    // 为 HMAC 计算重置哈希对象
    sha256_Sign.resetHMAC(ss, sizeof(ss));
    sha256_Sign.update(&sk_arr_tmp_sign[j], sizeof(sk_arr_tmp_sign[j]));
    sha256_Sign.finalizeHMAC(ss, sizeof(ss), hmac_tmp_sign, sizeof(hmac_tmp_sign));
    sk_arr_tmp_sign[j] = hmac_tmp_sign[j % 8];
  }

  // 自增随机数 r
  sha256_Sign.resetHMAC(ss, sizeof(ss));
  sha256_Sign.update(&r_arr, sizeof(r_arr));
  sha256_Sign.finalizeHMAC(ss, sizeof(ss), r_arr, sizeof(r_arr));
  // 计算哈希树 Ctrl Info 1 + Ctrl Info 2 + Ctrl Info 3 + r_arr
  // 随机 ctrl_info_1 ctrl_info_2 ctrl_info_3
  uint32_t ctrl_info_1[8] = { 0 };
  uint32_t ctrl_info_2[8] = { 0 };
  uint32_t ctrl_info_3[8] = { 0 };
  for (int i = 0; i < 8; i++) {
    ctrl_info_1[i] = random(4294967295);
    ctrl_info_2[i] = random(4294967295);
    ctrl_info_3[i] = random(4294967295);
  }

  // 计时函数 2
  unsigned int timecnt2;
  timecnt2 = micros();

  // 计算哈希值
  uint32_t ctrl_info_12[16] = { 0 };
  uint32_t ctrl_info_3r[16] = { 0 };
  uint32_t hash_left[8] = { 0 };
  uint32_t hash_right[8] = { 0 };
  uint32_t hash_lr[16] = { 0 };
  uint32_t hash_root[8] = { 0 };
  for(int i = 0; i < 8; i++){
    ctrl_info_12[i] = ctrl_info_1[i];
    ctrl_info_12[i + 8] = ctrl_info_2[i];
    ctrl_info_3r[i] = ctrl_info_3[i];
    ctrl_info_3r[i + 8] = r_arr[i];
  }
  sha256_Sign.clear();
  sha256_Sign.update(&ctrl_info_12, sizeof(ctrl_info_12));
  sha256_Sign.finalize(hash_left, sizeof(hash_left));
  sha256_Sign.clear();
  sha256_Sign.update(&ctrl_info_3r, sizeof(ctrl_info_3r));
  sha256_Sign.finalize(hash_right, sizeof(hash_right));
  for(int i = 0; i < 8; i++){
    hash_lr[i] = hash_left[i];
    hash_lr[i + 8] = hash_right[i];
  }
  sha256_Sign.clear();
  sha256_Sign.update(&hash_lr, sizeof(hash_lr));
  sha256_Sign.finalize(hash_root, sizeof(hash_root));

  // 根据消息个数求模，此处以 0 模拟
  uint32_t t = hash_root[0 % 8];

  // 进行签名
  uint32_t sig[32] = { 0 };
  for(uint32_t i = 1, count = 0; i != 0; i <<= 1, count++){
    if((t & i) != 0){
      uint32_t hash_tmp_sign[8] = { 0 };
      sha256_Sign.clear();
      sha256_Sign.update(&sk_arr_tmp_sign[count], sizeof(sk_arr_tmp_sign[count]));
      sha256_Sign.finalize(hash_tmp_sign, sizeof(hash_tmp_sign));
      sig[count] = hash_tmp_sign[count % 8];
      // printf("相同位 : %u, i 值: %u\n", count, i);
    }else{
      sig[count] = sk_arr_tmp_sign[count];
    }
  }

  // 计时函数 2 结束
  timecnt2 = micros() - timecnt2;
  printf("Sign 执行结束, 用时: %d 微秒\n", timecnt2);

  // ============Sign 执行结束============

  // ============3、verify 验证签名（单次）============
  printf("============3、verify 验证签名============\n");

  // 做哈希树运算
  SHA256 sha256_verify;

  // 计时函数 3
  unsigned int timecnt3;
  timecnt3 = micros();

  uint32_t ctrl_info_12_v[16] = { 0 };
  uint32_t ctrl_info_3r_v[16] = { 0 };
  uint32_t hash_left_v[8] = { 0 };
  uint32_t hash_right_v[8] = { 0 };
  uint32_t hash_lr_v[16] = { 0 };
  uint32_t hash_root_v[8] = { 0 };
  for(int i = 0; i < 8; i++){
    ctrl_info_12_v[i] = ctrl_info_1[i];
    ctrl_info_12_v[i + 8] = ctrl_info_2[i];
    ctrl_info_3r_v[i] = ctrl_info_3[i];
    ctrl_info_3r_v[i + 8] = r_arr[i];
  }
  sha256_verify.clear();
  sha256_verify.update(&ctrl_info_12_v, sizeof(ctrl_info_12_v));
  sha256_verify.finalize(hash_left_v, sizeof(hash_left_v));
  sha256_verify.clear();
  sha256_verify.update(&ctrl_info_3r_v, sizeof(ctrl_info_3r_v));
  sha256_verify.finalize(hash_right_v, sizeof(hash_right_v));
  for(int i = 0; i < 8; i++){
    hash_lr_v[i] = hash_left_v[i];
    hash_lr_v[i + 8] = hash_right_v[i];
  }
  sha256_verify.clear();
  sha256_verify.update(&hash_lr_v, sizeof(hash_lr_v));
  sha256_verify.finalize(hash_root_v, sizeof(hash_root_v));

  // 根据消息个数求模，此处以 0 模拟
  uint32_t t_v = hash_root_v[0 % 8];

  // 验证签名
  for(uint32_t i = 1, count = 0; i != 0; i <<= 1, count++){
    if((t_v & i) == 0){
      uint32_t hash_tmp_verify[8] = { 0 };
      sha256_verify.clear();
      sha256_verify.update(&sig[count], sizeof(sig[count]));
      sha256_verify.finalize(hash_tmp_verify, sizeof(hash_tmp_verify));
      sig[count] = hash_tmp_verify[count % 8];
    }
  }

  // 对 sig 再做一次 sha256
  uint32_t sig_verify[8] = { 0 };
  sha256_verify.clear();
  sha256_verify.update(&sig, sizeof(sig));
  sha256_verify.finalize(sig_verify, sizeof(sig_verify));

  // 对 BF 进行查询
  lookupSmartBF(sig_verify);

  // 计时函数 3 结束
  timecnt3 = micros() - timecnt3;
  printf("verify 执行结束, 用时: %d 微秒\n", timecnt3);
  
  printf("\n验证正确个数: %d, 验证错误个数: %d\n", TP, TN);


  delay(10000);
}
