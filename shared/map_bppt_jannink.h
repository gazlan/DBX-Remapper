/* ******************************************************************** **
** @@ B++ Tree Index Header File
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify : 
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

#ifndef  _BPPTIDX_HPP_
#define  _BPPTIDX_HPP_

#if _MSC_VER > 1000
#pragma once
#endif 

/*
 *  algorithm:
 *
 *    A B+tree implementation, with keys stored in internal nodes,
 *    and keys/record addresses stored in leaf nodes.  Each node is
 *    one sector in length, except the root node whose length is
 *    3 sectors.  When traversing the tree to insert a key, full
 *    children are adjusted to make room for possible new entries.
 *    Similarly, on deletion, half-full nodes are adjusted to allow for
 *    possible deleted entries.  Adjustments are first done by
 *    examining 2 nearest neighbors at the same level, and redistibuting
 *    the keys if possible.  If redistribution won't solve the problem,
 *    nodes are split/joined as needed.  Typically, a node is 3/4 full.
 *    On insertion, if 3 nodes are full, they are split into 4 nodes,
 *    each 3/4 full.  On deletion, if 3 nodes are 1/2 full, they are
 *    joined to create 2 nodes 3/4 full.
 *
 *    A LRR (least-recently-read) buffering scheme for nodes is used to
 *    simplify storage management, and, assuming some locality of reference,
 *    improve performance.
 *
 *    To simplify matters, both internal nodes and leafs contain the
 *    same fields.
 */

/* ******************************************************************** **
** @@ internal #defines
** ******************************************************************** */

#define MAX_KEY_CNT                    (16383)

/* ******************************************************************** **
** @@ enum E_BPPT_IDX_COND
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  : compare two keys and return:
** @  Notes  : CC_LT     key1 < key2
** @  Notes  : CC_GT     key1 > key2
** @  Notes  : CC_EQ     key1 = key2
** ******************************************************************** */

enum  E_BPPT_IDX_COND
{
   BPPT_IDX_COND_EQ =  0,
   BPPT_IDX_COND_GT =  1,
   BPPT_IDX_COND_LT = -1
};

typedef int (*CompareFunc)(const void* const pKey1,const void* const pKey2);

/* ******************************************************************** **
** @@ enum E_BPPT_IDX_ERR
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  : 
** ******************************************************************** */

enum E_BPPT_IDX_ERR
{
   BPPT_IDX_ERR_NONE            = 0,
   BPPT_IDX_ERR_KEY_NOT_FOUND   = 1,
   BPPT_IDX_ERR_DUP_KEYS        = 2,
   BPPT_IDX_ERR_SECTOR_SIZE     = 3,
   BPPT_IDX_ERR_FILE_NOT_OPEN   = 4,
   BPPT_IDX_ERR_FILE_EXISTS     = 5,
   BPPT_IDX_ERR_IO              = 6,
   BPPT_IDX_ERR_MEMORY          = 7,
   BPPT_IDX_ERR_CORRUPTED       = 8,
   BPPT_IDX_ERR_KEY_NULL_PTR    = 9,
   BPPT_IDX_ERR_HANDLE_NULL_PTR = 10
};

/* ******************************************************************** **
** @@ struct BPPT_INDEX_NODE
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  : 
** ******************************************************************** */

struct BPPT_INDEX_NODE
{
   WORD             _wLeaf:1;             // first bit = 1 if leaf
   WORD             _wClosed:1;
   WORD             _wCnt:14;             // count of keys present 

   // In this order: PREV, NEXT !
   DWORD             _dwPrev;             // prev node in sequence (leaf)
   DWORD             _dwNext;             // next node in sequence (leaf)
   DWORD             _dwLeft;             // Child LT

   // Count occurrences of [key,rec,childGE]
   char              _FirstKey;           // first occurrence 
   // DWORD          _dwKeyValue;         // Value of the Key
   // DWORD          _dwRight ;           // Child GE

   BPPT_INDEX_NODE()
   {
      _wClosed  = 0;
      _wLeaf    = 0;
      _wCnt     = 0;
      _dwPrev   = 0;
      _dwNext   = 0;
      _FirstKey = 0;
   };
};

/* ******************************************************************** **
** @@ struct BPPT_INDEX_BUFFER
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  : Location of node
** ******************************************************************** */

struct BPPT_INDEX_BUFFER
{
   // In this order: NEXT, PREV !
   BPPT_INDEX_BUFFER*      _pNext;              // next
   // Part to record in the Buf
   BPPT_INDEX_BUFFER*      _pPrev;              // previous
   DWORD                   _dwDiskAdr;          // on disk
   BPPT_INDEX_NODE*        _pMemNode;           // in memory
   bool                    _bValid;             // true if buffer contents valid
   bool                    _bModified;          // true if buffer modified

   BPPT_INDEX_BUFFER()
   {
      _pNext     = NULL;
      _pPrev     = NULL;
      _dwDiskAdr = 0;
      _pMemNode  = NULL; 
      _bValid    = false; 
      _bModified = false;
   };
};

/* ******************************************************************** **
** @@ struct BPPT_STAT_INFO
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

struct BPPT_STAT_INFO
{
   int   _iMaxHeight;      // maximum height attained
   int   _iNodesIns;       // number of nodes inserted
   int   _iNodesDel;       // number of nodes deleted
   int   _iKeysIns;        // number of keys inserted
   int   _iKeysDel;        // number of keys deleted
   int   _iDiskReads;      // number of disk reads
   int   _iDiskWrites;     // number of disk writes

   BPPT_STAT_INFO()
   {
      _iMaxHeight  = 0;
      _iNodesIns   = 0; 
      _iNodesDel   = 0; 
      _iKeysIns    = 0;  
      _iKeysDel    = 0;  
      _iDiskReads  = 0;
      _iDiskWrites = 0;
   }
};

/* ******************************************************************** **
** @@ struct BPPT_HANDLE_NODE
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  : One node for each open handle
** ******************************************************************** */

struct BPPT_HANDLE_NODE
{
   bool                 _bDuplicate;        
   bool                 _bFlushed;   
   BPPT_HANDLE_NODE*    _pPrev;              // previous node
   BPPT_HANDLE_NODE*    _pNext;              // next node
   HANDLE               _hFile;              // idx file 
   int                  _iKeySize;           // key length
   int                  _iSectorSize;        // block size for idx records
   CompareFunc          _pCompare;           // pointer to compare routine
   BPPT_INDEX_BUFFER    _Root;               // root of b-tree, room for 3 sets
   BPPT_INDEX_BUFFER    _Cache;              // head of buf list
   void*                _pHeap1;             // alloc'd resources 
   void*                _pHeap2;             // alloc'd resources 
   BPPT_INDEX_BUFFER    _GatherBuf;          // gather buffer, room for 3 sets
   BPPT_INDEX_BUFFER*   _pCurBuf;            // current location
   char*                _pCurKey;            // current key in current node
   DWORD                _dwMaxKeyCnt;        // minimum # keys in node
   int                  _iKeyEntrySize;      // sizeof key entry
   DWORD                _dwNextFreeAdr;      // next free b-tree record address

    BPPT_HANDLE_NODE();
   ~BPPT_HANDLE_NODE();
};

/* ******************************************************************** **
** @@ struct BPPT_INDEX_INFO
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

struct BPPT_INDEX_INFO
{
   bool           _bDuplicate;         
   bool           _bInitialized;         
   char           _pszIndexName[MAX_PATH + 1];  // name of index file
   int            _iKeySize;                    // length, in bytes, of key
   int            _iSectorSize;                 // size of sector on disk
   CompareFunc    _pCompare;                    // pointer to compare function
};

/* ******************************************************************** **
** @@ class BPPTreeIndex
** @  Copyrt : 
** @  Author : 
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

class BPPTreeIndex
{
   private:

      BPPT_HANDLE_NODE*       _pHandle;
      BPPT_HANDLE_NODE        _hList;           // list of hNodes
      BPPT_STAT_INFO          _StatInfo;        // statistics

   public:

      int               _iErr;  

   public:

       BPPTreeIndex();
      ~BPPTreeIndex();
            
      int               GetLastErr() const;
      const char* const DescribeError();

      bool  Open(const BPPT_INDEX_INFO& rInfo);
      void  Close();
      void  Flush();
      void  DeleteCurKey();
      bool  Insert  (const char* const pKey,DWORD dwValue);
      bool  Delete  (const char* const pKey);
      bool  Find    (const char* const pKey,DWORD* pValue = NULL);
      DWORD IncValue(const char* const pKey);

      bool  FindFirst(char* pKey = NULL,DWORD* pValue = NULL);
      bool  FindLast (char* pKey = NULL,DWORD* pValue = NULL);
      bool  FindPrev (char* pKey = NULL,DWORD* pValue = NULL);
      bool  FindNext (char* pKey = NULL,DWORD* pValue = NULL);

      int   CountKeyStat();
      const BPPT_STAT_INFO& Statistics() const;

   private:

      bool  LazyRead(DWORD dwAdr,BPPT_INDEX_BUFFER** pIdxBuf);
      void  LazyWrite(BPPT_INDEX_BUFFER* pBbuf);
      bool  Flush(BPPT_INDEX_BUFFER* pBuf);
      bool  FlushAll();
      DWORD Allocate();
      bool  AssignBuf(DWORD dwAdr,BPPT_INDEX_BUFFER** pIdxBuf);
      int   Search(BPPT_INDEX_BUFFER* pBuf,const char* const pKey,char** pMatchKey);
      void  ScatterRoot();
      bool  Scatter(BPPT_INDEX_BUFFER* pBuf,char* pKey,int iTempMax,BPPT_INDEX_BUFFER** pTempArr);
      void  GatherRoot();
      bool  Gather(BPPT_INDEX_BUFFER* pIdxBuf,char** pKey,BPPT_INDEX_BUFFER** pTmpBuf);

      inline DWORD Count(BPPT_INDEX_BUFFER* pBuf);
      inline void  SetCount(BPPT_INDEX_BUFFER* pBuf,DWORD dwCnt);
      inline void  Inc(BPPT_INDEX_BUFFER* pBuf);
      inline void  Inc(BPPT_INDEX_BUFFER* pBuf,DWORD dwCnt);
      inline void  Dec(BPPT_INDEX_BUFFER* pBuf);
      inline bool  Leaf(const BPPT_INDEX_BUFFER* const pBuf);
      inline void  SetLeaf(BPPT_INDEX_BUFFER* pBuf,bool bLeaf);
      inline DWORD Next(BPPT_INDEX_BUFFER* pBuf);
      inline void  SetNext(BPPT_INDEX_BUFFER* pBuf,DWORD dwNext);
      inline DWORD Prev(BPPT_INDEX_BUFFER* pBuf);
      inline void  SetPrev(BPPT_INDEX_BUFFER* pBuf,DWORD dwPrev);
      inline char* First(BPPT_INDEX_BUFFER* pBuf);
      inline char* Last(BPPT_INDEX_BUFFER* pBuf);
      inline char* Ptr(BPPT_INDEX_BUFFER* pBuf);
      inline DWORD ValueOF(char* pKey);
      inline void  SetValueOF(char* pKey,DWORD dwValue);
      inline DWORD Child_LT(char* pKey);
      inline void  SetChild_LT(char* pKey,DWORD dwValue);
      inline DWORD Child_GE(char* pKey);
      inline void  SetChild_GE(char* pKey,DWORD dwValue);
      inline int   KeysSize(int iCnt);
};

/* ******************************************************************** **
** @@ internal prototypes
** ******************************************************************** */

/* ******************************************************************** **
** @@ external global variables
** ******************************************************************** */

/* ******************************************************************** **
** @@ static global variables
** ******************************************************************** */

/* ******************************************************************** **
** @@ Global Function Prototypes
** ******************************************************************** */

#endif

/* ******************************************************************** **
** End of File
** ******************************************************************** */
