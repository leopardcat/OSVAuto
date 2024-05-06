# 操作系统形式化规约案例

本文档介绍uC/OS-II验证中形式化规约的表达。在下面的例子中，我们将分别展示C代码、Coq中的形式化规约、新验证工具拟使用的形式化规约语言、以及非形式化的性质表达。C代码从uC-OS/II的实现中摘取并经过简化。

## 任务控制块

### 源代码中的定义：

任务控制块在C代码中的定义如下：

```c
typedef struct os_tcb {
    struct os_tcb *OSTCBNext;
    struct os_tcb *OSTCBPrev;
    OS_EVENT      *OSTCBEventPtr;
    void          *OSTCBMsg;
    INT16U         OSTCBDly;
    INT16U         OSTCBStat;
    INT8U          OSTCBPrio;
    INT8U          OSTCBX;
    INT8U          OSTCBY;
    INT8U          OSTCBBitX;
    INT8U          OSTCBBitY;
} OS_TCB;
```

其中任务状态`OSTCBStat`使用bitmap表示：每一位代表一个关于状态的flag。如果没有任何flag被设置，则`OSTCBStat`的值为`OS_STAT_RDY`，代表该进程处于就绪态或正在等待时延（由`OSTCBDly`是否大于0决定）。事件状态通过设置`OS_STAT_SEM`，`OS_STAT_MBOX`，`OS_STAT_Q`或`OS_STAT_MUTEX`表示，分别对应该任务正在等待信号量、邮箱、消息队列和互斥量。一个任务最多只能等待一个事件，因此这四个flag中最多一个被设置。任务的挂起状态通过设置`OS_STAT_SUSPEND`表示。任务是否被挂起和是否等待事件是独立的：任务可能同时被挂起和等待事件，或挂起并没有等待事件，或等待事件并没有挂起。此外，很多事件同时设置了时间限制，同样存储在`OSTCBDly`中。

```c
#define  OS_STAT_RDY      0x0000  /* Ready to run         */
#define  OS_STAT_SEM      0x0001  /* Pending on semaphore */
#define  OS_STAT_MBOX     0x0002  /* Pending on mailbox   */
#define  OS_STAT_Q        0x0004  /* Pending on queue     */
#define  OS_STAT_SUSPEND  0x0008  /* Task is suspended    */
#define  OS_STAT_MUTEX    0x0010  /* Pending on mutex     */
```

所有任务的控制块存储在一个数组中，由任务的优先级作为索引（该系统不允许两个任务拥有相同的优先级，因此优先级可以作为任务的索引）：
```c
OS_EXT  OS_TCB           *OSTCBPrioTbl[OS_LOWEST_PRIO + 1];
```

此外，通过双向链表存储空闲的任务控制块：
```c
OS_EXT  OS_TCB           *OSTCBFreeList;
```

### Coq中的底层状态表示

系统的底层状态通常由类型为`val`的值组成，其中`val`的定义为：

```coq
Inductive val : Set :=
 | Vundef: val
 | Vnull : val
 | Vint32: int -> val
 | Vptr  : addrval -> val.
```

该定义的解释如下：每个`val`可能是`Vundef`, `Vnull`, `Vint32 n`或`Vptr p`，其中`n`是一个整数，`p`是一个地址。地址`addrval`的定义如下：

```coq
Definition addrval := (block * int32)%type
```
也就是说，每个地址的形式为`(b, n)`，其中`b`为内存块的索引，`n`为在该内存块中的偏移 (offset)。`addrval`和`val`的定义体现了内存模型的选择：内存地址和普通的32位整数不同，仅在相同的内存块中可以对指针运算(pointer arithmetic)进行推理。一般来说，每个内存块对应着一个数组或结构体。

任务控制块的底层状态建模为12个`val`组成的列表，对应着`OS_TCB`中的属性。每个列表中元素的含义由以下定义确定：
```coq
Definition V_OSTCBNext     (vl:vallist) := nth_val 0 vl.
Definition V_OSTCBPrev     (vl:vallist) := nth_val 1 vl.
Definition V_OSTCBEventPtr (vl:vallist) := nth_val 2 vl.
Definition V_OSTCBMsg      (vl:vallist) := nth_val 3 vl.
Definition V_OSTCBDly      (vl:vallist) := nth_val 4 vl.
Definition V_OSTCBStat     (vl:vallist) := nth_val 5 vl.
Definition V_OSTCBPrio     (vl:vallist) := nth_val 6 vl.
Definition V_OSTCBX        (vl:vallist) := nth_val 7 vl.
Definition V_OSTCBY        (vl:vallist) := nth_val 8 vl.
Definition V_OSTCBBitX     (vl:vallist) := nth_val 9 vl.
Definition V_OSTCBBitY     (vl:vallist) := nth_val 10 vl.
Definition V_OSTCBflag     (vl:vallist) := nth_val 11 vl.
```

此外，任务状态`V_OSTCBStat vl`表示为32位整数，和C代码中相同：
```coq
Definition OS_STAT_RDY := 0%Z.
Definition OS_STAT_SEM := 1%Z.
Definition OS_STAT_MBOX := 2%Z.
Definition OS_STAT_Q := 4%Z.
Definition OS_STAT_SUSPEND := 8%Z.
Definition OS_STAT_MUTEX := 16%Z.
```

### 新验证工具中的底层状态表示

在新验证工具中，以上类型和结构体的定义表达如下：

内存地址和底层数据的类型：
```c
struct addrval {
    int32u block;
    int32u offset
}
datatype val =
    Vundef | Vnull | Vint32(int32u n) | Vptr(addrval addr)
```

底层任务控制块的定义（出于目前工具的限制，我们统一用32位整数表示C代码中的8, 16, 32位整数）：
```
struct TCB {
    val next;
    val prev;
    addrval eptr;
    val msg;
    int32u dly;
    int32u stat;
    int32u prio;
    int32u x;
    int32u y;
    int32u bitx;
    int32u bity;
    int32u flag
}
```

任务状态常量的定义：
```
consts {
    OS_STAT_RDY = 0;
    OS_STAT_SEM = 1;
    OS_STAT_MBOX = 2;
    OS_STAT_Q = 4;
    OS_STAT_SUSPEND = 8;
    OS_STAT_MUTEX = 16;
}
```
可以看到，新验证工具允许类似C的结构体定义（`struct`关键词），以及函数式编程中常用的数据类型定义（`datatype`关键词）。常量通过`consts`关键词定义。

### Coq中的高层状态表示

任务的高层状态表示为四元组，分别代表任务的优先级、状态（是否挂起除外）、发送的消息和挂起状态。具体Coq定义如下：
```coq
Module abstcb.
  Definition B : Set := (priority * taskstatus * msg * susstatus)%type.
  Definition holder : B := (Int.zero, rdy, Vnull, false).
End abstcb.
```

其中`priority`, `msg`和`susstatus`都是已有类型的缩写：
```coq
Definition priority := int32.
Definition msg := val.
Definition susstatus := bool.
```

类型`taskstatus`的定义为：
```coq
Definition ecbid := addrval.

Inductive tcbstats :=
 | os_stat_sem: ecbid -> tcbstats
 | os_stat_q: ecbid -> tcbstats
 | os_stat_postq: ecbid -> tcbstats
 | os_stat_time:  tcbstats
 | os_stat_mbox: ecbid -> tcbstats
 | os_stat_mutexsem: ecbid -> tcbstats.

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> option int32 -> taskstatus.
```
这个定义的含义是：任务状态或者是`rdy`，或者是`wait(stat, dly)`的形式，其中`stat`有六种可能性：`os_stat_sem(ev)`, `os_stat_q(ev)`, `os_stat_postq(ev)`, `os_stat_time`, `os_stat_mbox(ev)`和`os_stat_mutexsem(ev)`。其中`os_stat_time`表示等待延时，其余五个情况表示等待事件，并且`ev`是对应事件控制块的地址。`dly`可能是`none`和`some(n)`，分别表示没有时间限制/时间限制为`n`个时间单位（在`os_stat_time`的情况下`dly`不能为`none`）。

所有任务的高层状态表示为一个任务ID到高层状态的映射，其中任务ID为内存地址（对应C程序中任务控制块的地址）：
```coq
Definition tid := addrval.

Program Instance TcbMap: PermMap tid ( priority * taskstatus * msg * susstatus) TcbMod.map :=
  { ... }.
```

### 新验证工具中的高层状态表示

在新验证工具中，任务状态类型的定义如下：

```c
datatype tcbstats = 
    os_stat_sem (addrval ev)
  | os_stat_q (addrval ev)
  | os_stat_postq (addrval ev)
  | os_stat_time
  | os_stat_mbox (addrval ev)
  | os_stat_mutexsem (addrval ev)

datatype taskstatus =
    rdy | wait(tcbstats stat, int32u time)
```

所有任务的高层状态使用验证工具基本库中的映射类型`Map`表示：
```c
typedef TCBMap = Map<addrval, struct AbsTCB>;
```

### 优先级位图

出于效率的考虑，uC/OS的实现使用优先级位图的方式存储哪些优先级的任务处于就绪态（可以被调度运行）。优先级位图由八个8位的整数表示，每个整数可以理解为bitmap，表示8个优先级的任务是否就绪，因此整个优先级位图可以表示64个任务是否就绪。此外，还有一个8位的整数，每一位表示8个优先级的任务是否至少一个就绪。优先级位图在C代码中的定义如下：
```c
OS_EXT  INT8U  OSRdyGrp;                   /* Ready list group     */
OS_EXT  INT8U  OSRdyTbl[OS_RDY_TBL_SIZE];  /* Table of ready tasks */
```

以下Coq定义表达了如何在优先级位图中查找某个给定优先级的任务是否就绪。给定优先级`prio`，首先获得`prio`的后三位`x`和前三位`y`，通过`x = prio & 7`和`y = prio >> 3`，然后获得优先级位图`tbl`中第`y`个元素`z`，最后查看`z`中第`x`个二进制位是否为1。

```coq
Definition prio_in_tbl (prio:int32) (tbl:vallist) :=
  forall x y z,
    x = prio &ᵢ ($ 7) -> y = Int.shru prio ($ 3) ->
    nth_val (nat_of_Z (Int.unsigned y)) tbl = Some (Vint32 z) -> 
    z &ᵢ (($ 1) <<ᵢ x) = (($ 1) <<ᵢ x).

Definition prio_not_in_tbl (prio:int32) (tbl:vallist) :=
  forall x y z,
    x = prio &ᵢ ($ 7) -> y = Int.shru prio ($ 3) ->
    nth_val (nat_of_Z (Int.unsigned y)) tbl = Some (Vint32 z) -> 
    z &ᵢ (($ 1) <<ᵢ x) = $ 0.
```

由于Coq的语法限制，以上表达不是很直观。在新验证工具中，这两个谓词的表达如下（由于工具的限制，还是用32位整数表示优先级位图中的元素）：
```c
predicate prio_in_tbl(int32u prio, int32u[] rtbl) {
    let x = prio & 7 in
        rtbl[prio >> 3] & (1 << x) == 1 << x
    end
}

predicate prio_not_in_tbl(int32u prio, int32u[] rtbl) {
    let x = prio & 7 in
        rtbl[prio >> 3] & (1 << x) == 0
    end
}
```

### 任务控制块的不变式：精化关系

不变式描述了任务控制块的高层和底层状态在每个接口函数调用前后都必须满足的性质，其中包括高层和底层状态本身的数据一致性，以及高层和底层状态之间数据一致（满足精化关系）。例如，高层和底层状态通过不同的方式表达任务状态：高层使用`datatype`的不同分支，底层使用bitmap的形式。它们之间的一致性需要使用不变式描述。例如，对于任务处于就绪态，高层和底层之间的关系在Coq中描述如下：

```coq
Definition RdyTCBblk vl rtbl (prio : priority) := 
  V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_in_tbl prio rtbl.

Definition RLH_RdyI_P vl rtbl abstcb :=
  forall prio, RdyTCBblk vl rtbl prio ->
               V_OSTCBStat vl = Some (V$ OS_STAT_RDY) /\
               V_OSTCBDly vl = Some (V$ 0) /\
               exists (m:msg), abstcb = (prio,rdy,m,false).

Definition RHL_RdyI_P  vl rtbl abstcb := 
  forall prio (m:msg), abstcb = (prio,rdy,m,false)->
               (RdyTCBblk vl rtbl prio /\
               V_OSTCBStat vl = Some (V$ OS_STAT_RDY)/\ 
               V_OSTCBDly vl = Some (V$ 0)).
```
在这些定义中，参数`vl`为底层任务控制块，`abstcb`为高层任务控制块，`rtbl`为优先级位图。`RdyTCBblk vl rtbl prio`表示底层任务控制块的优先级等于`prio`，并且这个优先级处于优先级位图中。`RLH_RdyI_P vl rtbl abstcb`表示如果底层的任务状态为`OS_STAT_RDY`，等待时间为0，并且该优先级处于优先级位图中，则对应的高层任务控制块状态为`rdy`，并且`susstatus`为`false`。反之，如果高层任务控制块状态为`rdy`，并且`susstatus`为`false`，则底层任务控制块满足相应的条件。

下面展示当任务等待时间时，高层和底层之间的对应关系：
```coq
Definition WaitTCBblk vl rtbl (prio : priority) t :=
  V_OSTCBPrio vl = Some (Vint32 prio) /\ prio_not_in_tbl prio rtbl /\ 
  V_OSTCBDly vl = Some (Vint32 t).

Definition RLH_Wait_P vl rtbl abstcb := 
  forall prio t,
    WaitTCBblk vl rtbl prio t ->
    V_OSTCBStat vl = Some (V$ OS_STAT_RDY) ->
    Int.ltu Int.zero t = true /\
      exists (m:msg), abstcb = (prio, wait os_stat_time (Some t), m, false).

Definition RHL_Wait_P vl rtbl abstcb := 
  forall prio t_opt (m:msg),
    abstcb = (prio, wait os_stat_time t_opt, m, false) ->
    exists t, 
      t_opt = Some t /\  
      WaitTCBblk vl rtbl prio t /\
      Int.ltu Int.zero t = true  /\
      V_OSTCBStat vl = Some (V$ OS_STAT_RDY).
```

这里`WaitTCBblk vl rtbl prio t`表示底层任务控制块的优先级等于`prio`，等待时间为`t`，并且这个优先级不处于优先级位图中。`RLH_Wait_P vl rtbl abstcb`表示如果底层任务状态为`OS_STAT_RDY`，并且该优先级不处于优先级位图中，则等待时间`t`一定大于0，对应的高层任务控制块状态为`wait os_stat_time (Some t)`，并且`susstatus`为`false`。反之，如果高层任务控制块状态为`wait os_stat_time t_opt`，并且`susstatus`为`false`，则底层任务控制块满足相应的条件。

类似地，可以定义其他任务状态下高层和底层任务控制块之间的对应关系。这些对应关系收集到以下定义：
```coq
Definition R_TCB_Status_P vl rtbl abstcb :=
  RLH_RdyI_P vl rtbl abstcb /\
  RHL_RdyI_P vl rtbl abstcb /\
  RLH_Suspend_P vl rtbl abstcb /\
  RHL_Suspend_P vl rtbl abstcb /\
  RLH_TCB_Status_Wait_P vl rtbl abstcb /\ 
  RHL_TCB_Status_Wait_P vl rtbl abstcb.
```
其中，`RLH_RdyI_P`和`RHL_RdyI_P`包含任务就绪的情况，`RLH_Suspend_P`和`RHL_Suspend_P`包含任务挂起（并且没有等待事件或时延）的情况，`RLH_TCB_Status_Wait_P`和`RHL_TCB_Status_Wait_P`包含任务等待事件或时延的情况（不论是否挂起），其中也包括以上的`RLH_Wait_P`和`RHL_Wait_P`条件。

在新验证工具中，以上定义的表达如下：

```c
predicate RLH_RdyI_P(struct TCB tcb, int32u[] rtbl, struct AbsTCB abstcb) {
    prio_in_tbl(tcb.prio, rtbl) ->
    tcb.stat == OS_STAT_RDY && tcb.dly == 0 &&
    abstcb.prio == tcb.prio && abstcb.stat == rdy && abstcb.sus == false
}

predicate RHL_RdyI_P(struct TCB tcb, int32u[] rtbl, struct AbsTCB abstcb) {
    abstcb.stat == rdy && abstcb.sus == false ->
    prio_in_tbl(tcb.prio, rtbl) && tcb.prio == abstcb.prio &&
    tcb.stat == OS_STAT_RDY && tcb.dly == 0
}

predicate RLH_Wait_P(struct TCB tcb, int32u[] rtbl, struct AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_RDY ->
    tcb.dly > 0 && abstcb.prio == tcb.prio &&
    abstcb.stat == wait(os_stat_time, tcb.dly) && abstcb.sus == false
}

predicate RHL_Wait_P(struct TCB tcb, int32u[] rtbl, struct AbsTCB abstcb) {
    abstcb.stat == wait(os_stat_time, tcb.dly) -> abstcb.sus == false ->
    prio_not_in_tbl(tcb.prio, rtbl) && tcb.dly > 0 && tcb.stat == OS_STAT_RDY
}

predicate R_TCB_Status_P(struct TCB tcb, int32u[] rtbl, struct AbsTCB abstcb) {
    RLH_RdyI_P(tcb, rtbl, abstcb) &&
    RHL_RdyI_P(tcb, rtbl, abstcb) &&
    RLH_Suspend_P(tcb, rtbl, abstcb) &&
    RHL_Suspend_P(tcb, rtbl, abstcb) &&
    RLH_TCB_Status_Wait_P(tcb, rtbl, abstcb) &&
    RHL_TCB_Status_Wait_P(tcb, rtbl, abstcb)
}
```

相比于Coq中的定义，这些定义减少了一些参数，并且完全省略了`RdyTCBBlk`和`WaitTCBBlk`的定义。此外，`RLH_Wait_P`和`RHL_Wait_P`中的全称量词也不再需要。这种写法有利于后续的SMT求解。

### 任务控制块的不变式：底层状态的一致性

除了高层和底层状态之间的精化关系，底层状态自身也满足一些一致性约束。任务控制块的底层状态满足的约束如下：

```coq
Definition RL_TCBblk_P vl := 
  exists prio x y bitx bity stat, 
    V_OSTCBPrio vl = Some (Vint32 prio) /\
    V_OSTCBX vl = Some (Vint32 x) /\ V_OSTCBY vl = Some (Vint32 y) /\
    V_OSTCBBitX vl = Some (Vint32 bitx) /\ V_OSTCBBitY vl = Some (Vint32 bity) /\
    V_OSTCBStat vl = Some (Vint32 stat) /\
    0 <= Int.unsigned prio < 64 /\
    prio &ᵢ ($ 7) = x /\
    prio >>ᵢ ($ 3) = y /\
    ($ 1) <<ᵢ x = bitx /\ ($ 1) <<ᵢ y = bity /\
    (
      (stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SUSPEND) \/
       stat = ($ OS_STAT_SEM) \/ stat = ($ OS_STAT_Q) \/
       stat = ($ OS_STAT_MBOX) \/ stat = ($ OS_STAT_MUTEX) \/
       stat = ($ OS_STAT_POSTQ) \/
       stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
       stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)
      ) /\
      exists eptr, V_OSTCBEventPtr vl = Some eptr /\
          (stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SUSPEND) -> eptr = Vnull)
    ).
```

以上条件表示：任务的优先级`prio`在0到63之间，属性`x`是优先级的后三位，属性`y`是优先级的前三位，属性`bitx`和`bity`分别表示1左移`x`和`y`位。此外，`stat`的取值只有给定的几种可能性，事件指针的值和任务状态的取值相关联。

该定义在新验证工具中的表达如下：

```c
predicate RL_TCBblk_P (struct TCB tcb) {
    0 <= tcb.prio && tcb.prio < 64 &&
    tcb.prio & 7 == tcb.x &&
    tcb.prio >> 3 == tcb.y &&
    1 << tcb.x == tcb.bitx &&
    1 << tcb.y == tcb.bity &&
    (tcb.stat == OS_STAT_RDY || tcb.stat == OS_STAT_SUSPEND ||
      tcb.stat == OS_STAT_SEM || tcb.stat == OS_STAT_Q ||
      tcb.stat == OS_STAT_MBOX || tcb.stat == OS_STAT_MUTEX ||
      tcb.stat == OS_STAT_SEM | OS_STAT_SUSPEND ||
      tcb.stat == OS_STAT_Q | OS_STAT_SUSPEND ||
      tcb.stat == OS_STAT_MBOX | OS_STAT_SUSPEND ||
      tcb.stat == OS_STAT_MUTEX | OS_STAT_SUSPEND) &&
    (tcb.stat == OS_STAT_RDY || tcb.stat == OS_STAT_SUSPEND) -> tcb.eptr == Vnull 
}
```

### 抽象操作

每个操作系统接口的实现对应到建模中高层和底层状态上的转换。我们以任务挂起接口函数`TaskSuspend`为例。以下是OSTaskSuspend的C代码（简化版本）：
```c
INT8U  OSTaskSuspend (INT8U prio)
{
    OS_TCB    *ptcb;
    if (prio == OS_IDLE_PRIO) {     /* Not allowed to suspend idle task */
        return (INT8U)(OS_TASK_SUSPEND_IDLE);
    }
    if (prio >= OS_LOWEST_PRIO) {   /* Task priority valid ?            */
        return (INT8U)(OS_PRIO_INVALID);
    }

    OS_ENTER_CRITICAL();
    ptcb = OSTCBPrioTbl[prio];
    if (ptcb == (OS_TCB *)0) {      /* Task to suspend must exist       */
        OS_EXIT_CRITICAL();
        return (INT8U)(OS_TASK_SUSPEND_PRIO);
    }
    if ((OSRdyTbl[ptcb->OSTCBY] &= ~ptcb->OSTCBBitX) == 0x00) {
        /* Make task not ready */
        OSRdyGrp &= ~ptcb->OSTCBBitY;
    }
    ptcb->OSTCBStat |= OS_STAT_SUSPEND;   /* Status of task is 'SUSPENDED' */
    OS_EXIT_CRITICAL();
    OS_Sched();
    return (OS_NO_ERR);
}
```
该代码的解释如下：`OSTaskSuspend`的输入为被挂起任务的优先级`prio`。该函数首先检查三个输入合法性条件，并在检查失败时返回相应的错误码：

* 如果输入优先级为空闲任务的优先级，则返回`OS_TASK_SUSPEND_IDLE`。

* 如果输入优先级越界（大于最低优先级），则返回`OS_PRIO_INVALID`。

* 如果输入优先级不存在对应的任务，则返回`OS_TASK_SUSPEND_PRIO`。

最后，如果三个检查都通过，执行任务挂起操作：首先更新优先级位图，将目标任务的优先级从优先级位图移除；然后更新目标任务的状态，添加挂起位。最后执行调度`OS_Sched`。注意代码从获取输入优先级的任务控制块`ptcb = OSTCBPrioTbl[prio]`一直到完成对任务控制块的修改都处于临界区中，但调度操作处于另一个临界区。

该函数的抽象描述在Coq中表示如下，对应**高层状态**上的检查和转换。我们先分别看三个输入合法性检查对应的抽象操作：
```coq
Definition tasksuspend_err_prio_is_idle (vl: vallist) (O1: osabst)
                                        (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_SUSPEND_IDLE))) /\
      O2 = Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (Int.eq (Int.repr OS_IDLE_PRIO) v3 = true)
      )
  end.
```
其中，`vl`是函数的输入参数，`O1`是初始的高层状态，返回值`rst`由两部分组成：`opv`是函数的返回值，`O2`是终止时的高层状态。该定义的解释如下：输入列表`vl`应包含一个元素`v3`。如果`v3`等于空闲任务的优先级（`Int.eq (Int.repr OS_IDLE_PRIO) v3 = true`），则高层状态保持不变（`O2 = Some O1`），并且函数的返回值为`OS_TASK_SUSPEND_IDLE`。

另外两个输入合法性检查对应的抽象操作类似：
```coq
Definition tasksuspend_err_prio_invalid (vl: vallist) (O1: osabst)
                                        (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_PRIO_INVALID))) /\
      O2 = Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        Int.ltu (Int.repr OS_LOWEST_PRIO) v3 = true
      )
  end.
```

```coq
Definition tasksuspend_err_no_such_tcb (vl: vallist) (O1: osabst)
                                       (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_TASK_SUSPEND_PRIO))) /\
      O2 = Some O1 /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (~ exists tid st msg sus, TcbMod.get tls tid = Some (v3, st, msg, sus))
        )
      )
  end.
```
在以上定义中，`tls`表示所有高层任务控制块的映射，因此`TcbMod.get tls tid`表示地址为`tid`的任务控制块。不存在`tid`使得`TcbMod.get tls tid = Some (v3, ...)`表示不存在优先级为`v3`的任务。

下面展示检查通过后对状态的修改：
```coq
Definition tasksuspend_succ (vl: vallist) (O1: osabst)
                            (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) =>
      opv = (Some (Vint32 (Int.repr OS_NO_ERR))) /\
      (exists v3,
        vl = ((Vint32 v3)::nil) /\
        (exists tls,
          get O1 abstcblsid = Some (abstcblist tls) /\
          (exists tid st msg sus,
            TcbMod.get tls tid = Some (v3, st, msg, sus) /\
            O2 = Some (set O1 abstcblsid (abstcblist (
                                    TcbMod.set tls tid (v3, st, msg, true))))
          )
        )
      )
  end.
```
在该定义中，首先通过`exists tid ...`获得对应优先级`v3`的任务控制块`tid`，然后定义终止状态`O2`为在`O1`的基础上将`tid`对应的任务控制块中的`susstatus`设为`true`。

最后，整个挂起函数的抽象规约表示如下：
```coq
Definition tasksuspendcode (vl: vallist) :=
  tasksuspend_err_prio_is_idle (|vl|) ??
  tasksuspend_err_prio_invalid (|vl|) ??
  tasksuspend_err_no_such_tcb (|vl|) ??
  (tasksuspend_succ (|vl|) ;; isched ;; END (Some (Vint32 (Int.repr NO_ERR)))).
```
该定义表示函数的执行可能有四种情况，分别对应着三个合法性检查失败和成功情况。在成功情况中，首先执行对高层状态的更新，然后执行调度（`isched`）。使用;;将两者分开表示它们是两个不同的原子操作，中间可能被其他并发执行的进程打断。

注意抽象操作并没有描述优先级位图的更新。这是因为优先级位图不处于高层状态中。挂起函数的正确性证明要求不变式被维护，其中就包括优先级位图中的信息和任务控制块中的信息一致。因此，对任务控制块中挂起状态的更新必然也需要对优先级位图进行更新。也就是说，对挂起函数进行正确性验证一方面保证了优先级位图相关的更新是正确的，另一方面将函数的行为做了相应的抽象（忽略掉优先级位图等实现细节），有利于理解和基于该行为描述验证更高层次的用户程序。


## 消息队列

消息队列为抽象状态和具体状态之间的区别提供了一个典型的案例。消息队列采用先进先出模式，具体状态表示为一个数组，并维护这个数组中的入队索引和出队索引。消息队列的具体状态对应着一下C代码定义：

```c
typedef struct os_q {
  struct os_q *OSQPtr;    /* Link to next queue control */
  void       **OSQStart;  /* Start of queue data */
  void       **OSQEnd;    /* End of queue data */
  void       **OSQIn;     /* Location where next message is inserted */
  void       **OSQOut;    /* Location where next message is extracted */
  INT16u     **OSQSize;   /* Maximum number of entries in queue */
  INT16u     **OSQEntries;  /* Actual number of entries in queue */
} 
```

这对应着以下Coq定义：
```coq
Definition V_OSQPtr      (vl:vallist) := nth_val 0 vl.
Definition V_OSQStart    (vl:vallist) := nth_val 1 vl.
Definition V_OSQEnd      (vl:vallist) := nth_val 2 vl.
Definition V_OSQIn       (vl:vallist) := nth_val 3 vl.
Definition V_OSQOut      (vl:vallist) := nth_val 4 vl.
Definition V_OSQSize     (vl:vallist) := nth_val 5 vl.
Definition V_OSQEntries  (vl:vallist) := nth_val 6 vl.
```

首先，我们定义`distance`函数：给定两个地址，我们计算它们之间相隔多少个32位的地址：

```coq
Definition distance (v1 v2:addrval) :=
  Int.unsigned (Int.divu (Int.sub (snd v2) (snd v1))
               (Int.repr (Z_of_nat (typelen (Tptr Tvoid))))).
```

这个定义解读如下：地址使用由`block`和`offset`组成的二元组表示；为了找到两个地址之间的距离，首先计算`offset`部分的差，然后除以`void *`的大小（一般为4个字节/32位）。

下面，我们给出一些基本的列表上的操作的定义：删除列表中前几个元素`vallist_post`和提取列表中前几个元素`vallist_pre`：
```coq
Fixpoint vallist_post (first:nat) (vl:vallist) :=
  match first with
    | 0%nat => vl
    | S n => match vl with 
               | nil => nil
               | v::vl' => vallist_post n vl'
             end
  end.
```

```coq
Fixpoint vallist_pre (last:nat) (vl:vallist):= 
  match last with
    | 0%nat=> nil
    | S n => match vl with
               | nil => nil
               | v::vl' => v::(vallist_pre n vl')
             end
  end.
```

使用`vallist_pre`和`vallist_post`，我们定义如何提取列表中的中间几个元素：
```coq
Definition vallist_seg (first last:nat) (vl:vallist) :=
  vallist_post first (vallist_pre last vl).
```
该函数将提取列表`vl`中的`[first,last)`区间（包含`first`，不包含`last`）。

抽象队列和具体队列之间的关系主要由以下函数描述：
```coq
Definition MatchLHMsgList osq msgtbl msgl := 
  exists qstart qin qout qsize d1 d2 qens,
    V_OSQStart osq = Some (Vptr qstart) /\ 
    V_OSQIn osq = Some (Vptr qin) /\
    V_OSQOut osq = Some (Vptr qout) /\ 
    V_OSQSize osq = Some (Vint32 qsize) /\
    V_OSQEntries osq = Some (Vint32 qens) /\
    d1 = distance qstart qout /\ 
    d2 = distance qstart qin /\
    (( d2 > d1 ->
       vallist_seg (nat_of_Z d1) (nat_of_Z d2) msgtbl = msgl) /\ 
     ( d2 < d1 ->
       (vallist_seg (nat_of_Z d1) 
                    (nat_of_Z (Int.unsigned qsize)) msgtbl)++
                    (vallist_seg 0 (nat_of_Z d2) msgtbl) = msgl) /\
     ( d2 = d1 ->
       (Int.eq qens Int.zero = true /\ msgl = nil) \/
       (Int.eq qens qsize = true /\
        (vallist_seg (nat_of_Z d1) 
                     (nat_of_Z (Int.unsigned qsize)) msgtbl)++
                     (vallist_seg 0 (nat_of_Z d2) msgtbl) = msgl)))
    /\ isptr_list msgl. 
```
这个定义的解释如下：

* 函数的三个参数分别为`osq`，对应着以上的`osq`结构体；`msgtbl`对应着具体消息队列的内容；`msgl`对应着抽象消息队列的内容。

* 首先，设`d1`为`qstart`和`qout`之间的距离，`d2`为`qstart`和`qin`之间的距离，可以分别理解为当前入队和出队位置在数组中的索引。

* 如果`d2 > d1`，说明入队索引在出队索引之后，因此具体消息队列的存储区间不包含数组的边界，可以简单地使用`vallist_seg`函数提取抽象消息队列，并令其等于`msgl`。

* 如果`d2 < d1`，说明入队索引在出队索引之前，因此具体消息队列的存储区间包含数组的边界。这样抽象消息队列由两部分组成：第一部分从出队索引到数组的末尾，第二部分从数组的开头到入队索引。

* 如果`d2 = d1`，有两种可能性：队列为空和队列是满的。队列为空通过检查`qens = 0`判断，在这种情况下抽象消息队列为空列表。队列是满的通过检查`qens = qsize`判断，在这种情况下抽象消息队列的计算和上一种情况类似。

* 最后，抽象消息队列`msgl`中的每一个元素是一个指针，指向包含消息内容的地址。
