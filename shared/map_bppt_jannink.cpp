/* ******************************************************************** **
** @@ B++ Tree Index Source File
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

/* ******************************************************************** **
**                uses pre-compiled headers
** ******************************************************************** */

#include "stdafx.h"

#include "file.h"
#include "map_bppt_jannink.h"

/* ******************************************************************** **
** @@                   internal #defines
** ******************************************************************** */

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

#ifdef _DEBUG
#define LINE_ERROR(iErrCode)     LineError(__LINE__,iErrCode)
#else
#define LINE_ERROR(iErrCode)     (iErrCode)
#endif

/* ******************************************************************** **
** @@                   internal prototypes
** ******************************************************************** */

/* ******************************************************************** **
** @@                   external global variables
** ******************************************************************** */

/* ******************************************************************** **
** @@                   static global variables
** ******************************************************************** */

/* ******************************************************************** **
** @@                   real code
** ******************************************************************** */

/* ******************************************************************** **
** @@ BPPT_HANDLE_NODE::BPPT_HANDLE_NODE()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Constructor
** ******************************************************************** */

BPPT_HANDLE_NODE::BPPT_HANDLE_NODE()
{
   _bDuplicate    = false;
   _bFlushed      = false;
   _pPrev         = NULL;
   _pNext         = NULL;
   _hFile         = INVALID_HANDLE_VALUE;
   _iKeySize      = 0;
   _iSectorSize   = 0;
   _pCompare      = NULL;
   _pHeap1        = NULL; 
   _pHeap2        = NULL; 
   _pCurBuf       = NULL;
   _pCurKey       = NULL;
   _dwMaxKeyCnt   = 0;   
   _iKeyEntrySize = 0; 
   _dwNextFreeAdr = 0; 
};

/* ******************************************************************** **
** @@ BPPT_HANDLE_NODE::~BPPT_HANDLE_NODE()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Destructor
** ******************************************************************** */

BPPT_HANDLE_NODE::~BPPT_HANDLE_NODE()
{
   delete _pHeap1;
   _pHeap1 = NULL;

   delete _pHeap2;
   _pHeap2 = NULL;
};

/* ******************************************************************** **
** @@ BPPTreeIndex::BPPTreeIndex()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Constructor
** ******************************************************************** */

BPPTreeIndex::BPPTreeIndex()
{
   _pHandle = NULL;
   _iErr    = 0;

   memset(&_hList,   0,sizeof(_hList));
   memset(&_StatInfo,0,sizeof(_StatInfo));
}

/* **************\n****************************************************** **
** @@ BPPTreeIndex::~BPPTreeIndex()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Destructor
** ******************************************************************** */

BPPTreeIndex::~BPPTreeIndex()
{
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Count()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::Count(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return 0;
   }

   return pBuf->_pMemNode->_wCnt;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetCount()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetCount(BPPT_INDEX_BUFFER* pBuf,DWORD dwCnt)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   pBuf->_pMemNode->_wCnt = dwCnt;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Inc()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::Inc(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   ++pBuf->_pMemNode->_wCnt;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Inc()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

#pragma warning(disable: 4244)   // '+=' : conversion from 'unsigned long' to 'unsigned short', possible loss of data
void BPPTreeIndex::Inc(BPPT_INDEX_BUFFER* pBuf,DWORD dwCnt)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   pBuf->_pMemNode->_wCnt += dwCnt;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Dec()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::Dec(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      ASSERT(0);
      return;
   }

   --pBuf->_pMemNode->_wCnt;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Leaf()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

bool BPPTreeIndex::Leaf(const BPPT_INDEX_BUFFER* const pBuf)
{
   if (!pBuf)
   {
      // Error !
      return false;
   }

   return pBuf->_pMemNode->_wLeaf != 0;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetLeaf()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetLeaf(BPPT_INDEX_BUFFER* pBuf,bool bLeaf)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   pBuf->_pMemNode->_wLeaf = bLeaf  ?  1  :  0;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Next()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::Next(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return 0;
   }

   return pBuf->_pMemNode->_dwNext;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetNext()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetNext(BPPT_INDEX_BUFFER* pBuf,DWORD dwNext)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   pBuf->_pMemNode->_dwNext = dwNext;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Prev()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::Prev(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return 0;
   }

   return pBuf->_pMemNode->_dwPrev;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetPrev()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetPrev(BPPT_INDEX_BUFFER* pBuf,DWORD dwPrev)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   pBuf->_pMemNode->_dwPrev = dwPrev;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::First()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

char* BPPTreeIndex::First(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return NULL;
   }

   return &pBuf->_pMemNode->_FirstKey;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Last()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

char* BPPTreeIndex::Last(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return NULL;
   }

   #pragma warning (disable: 4710)  // function 'unsigned long __thiscall BPPTreeIndex::Count(struct BPPT_INDEX_BUFFER *)' not inlined
   return First(pBuf) + (Count(pBuf) - 1) * _pHandle->_iKeyEntrySize;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Ptr()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

char* BPPTreeIndex::Ptr(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return NULL;
   }

   return (char*)pBuf->_pMemNode;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::ValueOF()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::ValueOF(char* pKey)
{
   if (!pKey)
   {
      // Error !
      ASSERT(0);
      return 0;
   }

   return *(DWORD*)(pKey + _pHandle->_iKeySize); 
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetValueOF()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetValueOF(char* pKey,DWORD dwValue)
{
   if (!pKey)
   {
      // Error !
      return;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return;
   }

   *(DWORD*)(pKey + _pHandle->_iKeySize) = dwValue;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Child_LT()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::Child_LT(char* pKey)
{
   return *(DWORD*)(pKey - sizeof(DWORD));
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetChild_LT()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetChild_LT(char* pKey,DWORD dwValue)
{
   if (!pKey)
   {
      // Error !
      return;
   }

   *(DWORD*)(pKey - sizeof(DWORD)) = dwValue;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Child_GE()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::Child_GE(char* pKey)
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   return *(DWORD*)(pKey + _pHandle->_iKeySize + sizeof(DWORD));
}

/* ******************************************************************** **
** @@ BPPTreeIndex::SetChild_GE()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::SetChild_GE(char* pKey,DWORD dwValue)
{
   if (!pKey)
   {
      // Error !
      return;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return;
   }

   *(DWORD*)(pKey + _pHandle->_iKeySize + sizeof(DWORD)) = dwValue;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::KeysSize()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

int BPPTreeIndex::KeysSize(int iCnt) 
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return 0;
   }

   return iCnt * _pHandle->_iKeyEntrySize;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Open()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : ERR_OK                     - open was successful
** @  Notes  : BPPT_IDX_ERR_MEMORY        - insufficient memory
** @  Notes  : BPPT_IDX_ERR_SECTOR_SIZE   - sector size too small or not 0 mod 4
** @  Notes  : BPPT_IDX_ERR_FILE_NOT_OPEN - unable to open index file
** ******************************************************************** */

bool BPPTreeIndex::Open(const BPPT_INDEX_INFO& rInfo)
{
   if ((rInfo._iSectorSize < sizeof(BPPT_HANDLE_NODE)) || (rInfo._iSectorSize % 4))
   {
      _iErr = BPPT_IDX_ERR_SECTOR_SIZE;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   // determine sizes and offsets
   // leaf/n, prev, next, [CHILD_LT,key,rec]... CHILD_GE
   // ensure that there are at least 3 children/parent for gather/scatter
   // MAX_CNT - maximum number of keys in a node
   const int   MAX_CNT  = (rInfo._iSectorSize - (sizeof(BPPT_INDEX_NODE) - sizeof(char))) / (sizeof(DWORD) + rInfo._iKeySize + sizeof(DWORD));

   if ((MAX_CNT < 6) || (MAX_CNT > MAX_KEY_CNT))
   {
      _iErr = BPPT_IDX_ERR_SECTOR_SIZE;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   // copy parms to hNode
   BPPT_HANDLE_NODE*     pNode = new BPPT_HANDLE_NODE;

   if (!pNode)
   {
      _iErr = BPPT_IDX_ERR_MEMORY;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   pNode->_iKeySize    = rInfo._iKeySize;
   pNode->_iSectorSize = rInfo._iSectorSize;
   pNode->_pCompare    = rInfo._pCompare;
   pNode->_bDuplicate  = rInfo._bDuplicate;

   // CHILD_LT, key, rec
   pNode->_iKeyEntrySize = sizeof(DWORD) + pNode->_iKeySize + sizeof(DWORD);
   pNode->_dwMaxKeyCnt   = MAX_CNT;

   // Allocate buflist.
   // During insert/delete, need simultaneous access to 7 buffers:
   // - 4 adjacent child bufs
   // - 1 parent buf
   // - 1 next sequential link
   // - 1 lastGE
   const int   BUF_CNT = 7;

   pNode->_pHeap1 = (void*)new char[BUF_CNT * sizeof(BPPT_INDEX_BUFFER)];

   if (!pNode->_pHeap1)
   {
      delete pNode;
      pNode = NULL;

      _iErr = BPPT_IDX_ERR_MEMORY;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   memset(pNode->_pHeap1,0,BUF_CNT * sizeof(BPPT_INDEX_BUFFER));

   BPPT_INDEX_BUFFER*      pBuf = (BPPT_INDEX_BUFFER*)pNode->_pHeap1;

   // Allocate bufs.
   // We need space for the following:
   // - BUF_CNT buffers, of size sectorSize
   // - 1 buffer for root, of size 3 * sectorSize
   // - 1 buffer for gbuf, size 3 * sectorsize + 2 extra keys
   //   to allow for LT pointers in last 2 nodes when gathering 3 full nodes
   pNode->_pHeap2 = (void*)new char[(BUF_CNT + 6) * pNode->_iSectorSize + 2 * pNode->_iKeyEntrySize];

   if (!pNode->_pHeap2)
   {
      delete pNode->_pHeap1;
      pNode->_pHeap1 = NULL;

      delete pNode;
      pNode = NULL;
      
      _iErr = BPPT_IDX_ERR_MEMORY;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   memset(pNode->_pHeap2,0,(BUF_CNT + 6) * pNode->_iSectorSize + 2 * pNode->_iKeyEntrySize);

   BPPT_INDEX_NODE*     pINode = (BPPT_INDEX_NODE*)pNode->_pHeap2;

   // Initialize Buflist
   pNode->_Cache._pNext = pBuf;
   pNode->_Cache._pPrev = pBuf + (BUF_CNT - 1);

   for (int ii = 0; ii < BUF_CNT; ++ii)
   {
      if (!ii)
      {
         pBuf->_pPrev = NULL;
      }
      else
      {
         pBuf->_pPrev = pBuf - 1;
      }
         
      if (ii == (BUF_CNT - 1))
      {
         pBuf->_pNext = NULL;
      }
      else
      {
         pBuf->_pNext = pBuf + 1;
      }

      pBuf->_bModified = false;
      pBuf->_bValid    = false;
      pBuf->_pMemNode  = pINode;

      pINode = (BPPT_INDEX_NODE*)((char*)pINode + pNode->_iSectorSize);

      ++pBuf;
   }

   pNode->_Cache._pNext->_pPrev = &pNode->_Cache;
   pNode->_Cache._pPrev->_pNext = &pNode->_Cache;

   // Initialize root
   BPPT_INDEX_BUFFER*   pRoot = &pNode->_Root;

   pRoot->_pMemNode = pINode;

   pINode = (BPPT_INDEX_NODE*)((char*)pINode + 3 * pNode->_iSectorSize);

   pNode->_GatherBuf._pMemNode = pINode;      // done last to include extra 2 keys

   pNode->_pCurBuf = NULL;
   pNode->_pCurKey = NULL;

   pNode->_hFile = CreateFile(rInfo._pszIndexName,OPEN_EXISTING);

   DWORD    dwFileSizeLo = GetFileSizeLo(pNode->_hFile);

   if ((pNode->_hFile != INVALID_HANDLE_VALUE) && dwFileSizeLo)
   {
      // Set Temporary - for Info Params !
      _pHandle = pNode;

      // Open an existing database
      if (!LazyRead(0,&pRoot))
      {
         delete pNode->_pHeap1;
         pNode->_pHeap1 = NULL;

         delete pNode->_pHeap2;
         pNode->_pHeap2 = NULL;

         CloseHandle(pNode->_hFile);
         pNode->_hFile = INVALID_HANDLE_VALUE;

         delete pNode;
         pNode = NULL;

         _pHandle = NULL;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }

      if (!pRoot->_pMemNode->_wClosed)
      {
         _iErr = BPPT_IDX_ERR_CORRUPTED;

         delete pNode->_pHeap1;
         pNode->_pHeap1 = NULL;

         delete pNode->_pHeap2;
         pNode->_pHeap2 = NULL;

         CloseHandle(pNode->_hFile);
         pNode->_hFile = INVALID_HANDLE_VALUE;

         delete pNode;
         pNode = NULL;

         _pHandle = NULL;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }

/*     
      if (!_pHandle->_bFlushed)
      {
         TRACE("File: %s, Line: %d, Index Error ! File wasn't properly closed !\n",__FILE__,__LINE__);

         delete pNode->_pHeap1;
         pNode->_pHeap1 = NULL;

         delete pNode->_pHeap2;
         pNode->_pHeap2 = NULL;

         delete pNode;
         pNode = NULL;

         _pHandle = NULL;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
         return false;
      }
*/

      pNode->_dwNextFreeAdr = SetFilePointerEOF(pNode->_hFile);

      if (pNode->_dwNextFreeAdr == -1)
      {
         delete pNode->_pHeap1;
         pNode->_pHeap1 = NULL;

         delete pNode->_pHeap2;
         pNode->_pHeap2 = NULL;

         CloseHandle(pNode->_hFile);
         pNode->_hFile = INVALID_HANDLE_VALUE;

         delete pNode;
         pNode = NULL;

         _pHandle = NULL;

         _iErr = BPPT_IDX_ERR_IO;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }
   }
   else 
   {
      if (pNode->_hFile != INVALID_HANDLE_VALUE)
      {
         CloseHandle(pNode->_hFile);
         pNode->_hFile = INVALID_HANDLE_VALUE;
      }

      pNode->_hFile = CreateFile(rInfo._pszIndexName,CREATE_ALWAYS);

      if (pNode->_hFile != INVALID_HANDLE_VALUE)
      {
         // initialize root
         memset(pRoot->_pMemNode,0,3 * pNode->_iSectorSize);

         SetLeaf(pRoot,true);

         pNode->_dwNextFreeAdr = 3 * pNode->_iSectorSize;
      }
      else
      {
         // something's wrong
         delete pNode->_pHeap1;
         pNode->_pHeap1 = NULL;

         delete pNode->_pHeap2;
         pNode->_pHeap2 = NULL;

         CloseHandle(pNode->_hFile);
         pNode->_hFile = INVALID_HANDLE_VALUE;

         delete pNode;
         pNode = NULL;

         _pHandle = NULL;

         _iErr = BPPT_IDX_ERR_FILE_NOT_OPEN;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }
   }

   // Sppend node to hList
   if (_hList._pNext)
   {
      pNode->_pPrev = _hList._pNext;
      pNode->_pNext = &_hList;

      pNode->_pPrev->_pNext = pNode;
      pNode->_pNext->_pPrev = pNode;
   }
   else
   {
      // first item in hList
      pNode->_pNext = &_hList;
      pNode->_pPrev = pNode->_pNext;

      _hList._pPrev = pNode;
      _hList._pNext = _hList._pPrev;
   }

   _pHandle = pNode;

   _pHandle->_Root._pMemNode->_wClosed = 0;

   if (!Flush(&_pHandle->_Root))
   {
      // something's wrong
      delete pNode->_pHeap1;
      pNode->_pHeap1 = NULL;

      delete pNode->_pHeap2;
      pNode->_pHeap2 = NULL;

      CloseHandle(pNode->_hFile);
      pNode->_hFile = INVALID_HANDLE_VALUE;

      delete pNode;
      pNode = NULL;

      _pHandle = NULL;

      _iErr = BPPT_IDX_ERR_FILE_NOT_OPEN;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   _pHandle->_Root._bModified = true;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Close()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : ERR_OK - file closed, resources deleted
** ******************************************************************** */

void BPPTreeIndex::Close()
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return;
   }

   if (_pHandle->_Root._pMemNode)
   {
      _pHandle->_Root._pMemNode->_wClosed = 1;
      _pHandle->_Root._bModified          = true;
   }   

   // Remove from list
   if (_pHandle->_pNext)
   {
      _pHandle->_pNext->_pPrev = _pHandle->_pPrev;
      _pHandle->_pPrev->_pNext = _pHandle->_pNext;
   }

   // Flush Idx
   if (_pHandle->_hFile != INVALID_HANDLE_VALUE)
   {
      FlushAll();
      CloseHandle(_pHandle->_hFile);
      _pHandle->_hFile = INVALID_HANDLE_VALUE;
   }

   if (_pHandle->_pHeap2)
   {
      delete _pHandle->_pHeap2;
      _pHandle->_pHeap2 = NULL;
   }

   if (_pHandle->_pHeap1)
   {
      delete _pHandle->_pHeap1;
      _pHandle->_pHeap1 = NULL;
   }

   delete _pHandle;
   _pHandle = NULL;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Insert()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : ERR_OK      - operation successful
** @  Notes  : BPPT_IDX_ERR_DUP_KEYS - duplicate keys
** ******************************************************************** */

bool BPPTreeIndex::Insert
(                             
   const char* const       pKey,             // key to insert
   DWORD                   dwValue           // record address
)
{
   if (!pKey)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_KEY_NULL_PTR;
      return false;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   BPPT_INDEX_BUFFER*      pTempBuf[4];

   memset(pTempBuf,0,sizeof(BPPT_INDEX_BUFFER*) * 4);

   // Check for full root
   BPPT_INDEX_BUFFER*      pRoot = &_pHandle->_Root;

   if (Count(pRoot) == (3 * _pHandle->_dwMaxKeyCnt))
   {
      // gather root and scatter to 4 bufs
      // this increases b-tree height by 1
      GatherRoot();

      if (!Scatter(pRoot,First(pRoot),0,pTempBuf))
      {
         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
         return false;
      }
   }

   DWORD    dwLast_GE     = 0;         // last CHILD_GE traversed
   DWORD    dwLast_GE_Key = 0;         // last CHILD_GE Key traversed

   bool     bLast_GE = false;          // true if GE branch taken
   bool     bLast_LT = false;          // true if LT branch taken after GE branch

   int      iTreeHeight = 0;           // height of tree

   BPPT_INDEX_BUFFER*      pBuf   = pRoot;
   char*             pFound = NULL;     // match key
                  
   #pragma warning (disable: 4127)    // conditional expression is constant                                    
   while (true)
   {
      if (Leaf(pBuf))
      {
         // in leaf, and there' room guaranteed
         if (iTreeHeight > _StatInfo._iMaxHeight)
         {
            _StatInfo._iMaxHeight = iTreeHeight;
         }

         // set pFound to point to insertion point
         int   iCondition = Search(pBuf,pKey,&pFound);

         if (Count(pBuf))
         {
            if (!_pHandle->_bDuplicate)
            {
               switch (iCondition)
               {
                  case BPPT_IDX_COND_LT:  // *pKey < *pFound
                  {
                     if (_pHandle->_pCompare(pKey,pFound) == BPPT_IDX_COND_EQ)
                     {
                        _iErr = BPPT_IDX_ERR_DUP_KEYS;
// Don't report about duplicates
//                        TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                        return false;
                     }
      
                     // Insert It at Found Point   
                     break;
                  }
                  case BPPT_IDX_COND_EQ:  // *pKey = *pFound
                  {
                     _iErr = BPPT_IDX_ERR_DUP_KEYS;
// Don't report about duplicates
//                     TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                     return false;
                  }
                  case BPPT_IDX_COND_GT:  // *pKey > *pFound
                  {
                     if (_pHandle->_pCompare(pKey,pFound) == BPPT_IDX_COND_EQ)
                     {
                        _iErr = BPPT_IDX_ERR_DUP_KEYS;
// Don't report about duplicates
//                        TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                        return false;
                     }                                            

                     pFound += KeysSize(1);
                     break;
                  }
               } 
            }
            else
            {
               if (iCondition == BPPT_IDX_COND_GT)
               {
                  pFound += KeysSize(1);
               }
            }
         }

         // shift items GE key to right
         DWORD    keyOff = pFound - First(pBuf);

         int   iLength = KeysSize(Count(pBuf)) - keyOff;   // length to shift

         if (iLength)
         {  
            memmove(pFound + KeysSize(1),pFound,iLength);
         }

         // insert new key
         memcpy(pFound,pKey,_pHandle->_iKeySize);

         SetValueOF(pFound,dwValue);
         SetChild_GE(pFound,0);
         Inc(pBuf);

         LazyWrite(pBuf);

         // if new key is first key, then fixup lastGE key
         if (!keyOff && bLast_LT)
         {
            BPPT_INDEX_BUFFER*   pTempBuf;

            if (!LazyRead(dwLast_GE,&pTempBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            char*    pTempKey = First(pTempBuf) + dwLast_GE_Key;

            memcpy(pTempKey,pKey,_pHandle->_iKeySize);

            SetValueOF(pTempKey,dwValue);

            LazyWrite(pTempBuf);
         }

         ++_StatInfo._iKeysIns;
         break;
      }
      else
      {
         // internal node, descend to child
         BPPT_INDEX_BUFFER*      pChildBuf = NULL; // child buf

         ++iTreeHeight;

         // read child
         int   iCond = Search(pBuf,pKey,&pFound);

         if (iCond < 0)
         {
            if (!LazyRead(Child_LT(pFound),&pChildBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }
         }
         else
         {
            if (!LazyRead(Child_GE(pFound),&pChildBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }
         }

         // check for room in child
         if (Count(pChildBuf) == _pHandle->_dwMaxKeyCnt)
         {
            // gather 3 bufs and scatter
            if (!Gather(pBuf,&pFound,pTempBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            if (!Scatter(pBuf,pFound,3,pTempBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            // read child
            iCond = Search(pBuf,pKey,&pFound);

            if (iCond < 0)
            {
               if (!LazyRead(Child_LT(pFound),&pChildBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&pChildBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }                     
            }
         }

         if (iCond >= 0 || pFound != First(pBuf))
         {
            bLast_GE = true;
            bLast_LT = false;

            dwLast_GE = pBuf->_dwDiskAdr;

            dwLast_GE_Key = pFound - First(pBuf);

            if (iCond < 0)
            {
               dwLast_GE_Key -= KeysSize(1);
            }
         }
         else
         {
            if (bLast_GE)
            {
               bLast_LT = true;
            }
         }

         pBuf = pChildBuf;
      }
   }

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Delete()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : rec               - record address deleted
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

bool BPPTreeIndex::Delete(const char* const pKey)  // key to delete
{
   if (!pKey)
   {
      // Error !
      return false;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   char*                   pFound    = NULL; // match key 
   DWORD                   keyOff    = 0;
   DWORD                   lastGE    = 0;     // last CHILD_GE traversed
   DWORD                   lastGEkey = 0;     // last CHILD_GE key traversed

   BPPT_INDEX_BUFFER*      pRoot = &_pHandle->_Root;
   BPPT_INDEX_BUFFER*      pGBuf = &_pHandle->_GatherBuf;

   bool     lastGEvalid = false;    // true if GE branch taken
   bool     lastLTvalid = false;    // true if LT branch taken after GE branch

   BPPT_INDEX_BUFFER*      pBuf = pRoot;

   #pragma warning (disable: 4127)    // conditional expression is constant                                    
   while (true)
   {
      if (Leaf(pBuf))
      {
         // set pFound to point to deletion point
         if (Search(pBuf,pKey,&pFound) != BPPT_IDX_COND_EQ)
         {
            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

            return false;
         }

         // shift items GT key to left 
         keyOff = pFound - First(pBuf);

         // length to shift
         int      iLen = KeysSize(Count(pBuf) - 1) - keyOff;

         if (iLen)
         {
            memmove(pFound,pFound + KeysSize(1),iLen);
         }

         Dec(pBuf);

         LazyWrite(pBuf);

         // if deleted key is first key, then fixup lastGE key
         if (!keyOff && lastLTvalid)
         {
            BPPT_INDEX_BUFFER*      pTmpBuf;

            if (!LazyRead(lastGE,&pTmpBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            char*       pTmpKey = First(pTmpBuf) + lastGEkey;

            memcpy(pTmpKey,pFound,_pHandle->_iKeySize);

            SetValueOF(pTmpKey,ValueOF(pFound));

            LazyWrite(pTmpBuf);
         }

         ++_StatInfo._iKeysDel;
         break;
      }
      else
      {
         int   iCond = 0;    // condition code

         // internal node, descend to child
         BPPT_INDEX_BUFFER*      cbuf;      // child buf

         // read child
         if (!_pHandle->_bDuplicate)
         {
            if ((iCond = Search(pBuf,pKey,&pFound)) < 0)
            {
               if (!LazyRead(Child_LT(pFound),&cbuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&cbuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
         }
         else
         {
            if ((iCond = Search(pBuf,pKey,&pFound)) <= 0)
            {
               if (!LazyRead(Child_LT(pFound),&cbuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&cbuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
         }

         BPPT_INDEX_BUFFER*      pTempBuf[4];

         memset(pTempBuf,0,sizeof(BPPT_INDEX_BUFFER*) * 4);

         // check for room to delete
         if (Count(cbuf) == (_pHandle->_dwMaxKeyCnt >> 1))
         {
            // gather 3 bufs and scatter
            if (!Gather(pBuf,&pFound,pTempBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            // if last 3 bufs in root, and count is low enough...
            if (pBuf == pRoot && Count(pRoot) == 2 && Count(pGBuf) < ((3 * (3 * _pHandle->_dwMaxKeyCnt)) >> 2))
            {
               // collapse tree by one level
               ScatterRoot();
               _StatInfo._iNodesDel += 3;
               continue;
            }

            if (!Scatter(pBuf,pFound,3,pTempBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            // read child 
            if ((iCond = Search(pBuf,pKey,&pFound)) < 0)
            {
               if (!LazyRead(Child_LT(pFound),&cbuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound), &cbuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
         }

         if (iCond >= 0 || pFound != First(pBuf))
         {
            lastGEvalid = true;
            lastLTvalid = false;

            lastGE    = pBuf->_dwDiskAdr;
            lastGEkey = pFound - First(pBuf);

            if (iCond < 0)
            {
               lastGEkey -= KeysSize(1);
            }
         }
         else
         {
            if (lastGEvalid)
            {
               lastLTvalid = true;
            }
         }

         pBuf = cbuf;
      }
   }

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::DeleteCurKey()
** @  Copyrt : 
** @  Author :
** @  Modify : 
** @  Update :
** @  Notes  : rec               - record address deleted
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

void BPPTreeIndex::DeleteCurKey()
{
   char*    pNextKey = new char[_pHandle->_iKeySize];

   if (!pNextKey)
   {
      // Error !
      return;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      delete pNextKey;
      pNextKey = NULL;
      return;
   }

   char*    pFound = _pHandle->_pCurKey;     // match key

   if (!_pHandle->_bDuplicate)
   {
      memcpy(pNextKey,pFound,_pHandle->_iKeySize);

      Delete(pNextKey);
      
      delete pNextKey;
      pNextKey = NULL;
      
      return;
   }

   BPPT_INDEX_BUFFER*      pBuf = _pHandle->_pCurBuf; 
   
   if (pBuf)
   {
      if (Leaf(pBuf))
      {           
         // shift items GT key to left
         DWORD    dwKeyOfs = pFound - First(pBuf);

         int   iLen = KeysSize(Count(pBuf) - 1) - dwKeyOfs;

         // Length to shift
         if (iLen)
         {
            memmove(pFound,pFound + KeysSize(1),iLen);
         }

         Dec(pBuf);

         DWORD    NextValue = 0;

         if (Count(pBuf) && !iLen)
         {
            _pHandle->_pCurKey -= KeysSize(1);

            if (!FindNext(pNextKey,&NextValue))
            {
               if (!FindLast(pNextKey,&NextValue))
               {
                  // Error !
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               }
            }
         }

         if (!iLen && !Count(pBuf))               
         {
            if (!FindNext(pNextKey,&NextValue))
            {
               if (!FindLast(pNextKey,&NextValue))
               {
                  // Error !
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               }
            }
         }
         
         delete pNextKey;
         pNextKey = NULL;

         LazyWrite(pBuf);
         ++_StatInfo._iKeysDel;         
      }      
   }
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Find()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify : 
** @  Update :
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

bool BPPTreeIndex::Find
(
   const char* const          pKey,    // key to find
   DWORD*                     pValue   // record address
)
{
   if (IsBadWritePtr(pValue,sizeof(DWORD)))
   {
      // Error !
     ASSERT(0);
     return false;
   }

   *pValue = 0;   // Reset

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   BPPT_INDEX_BUFFER*      pBuf   = &_pHandle->_Root;    // buffer
   char*             pFound = NULL;                // matched key

   // Find key, and return address
   #pragma warning (disable: 4127)    // conditional expression is constant                                    
   while (true)   
   {
      if (Leaf(pBuf))
      {
         if (_pHandle->_bDuplicate)
         {
            while (!Count(pBuf))
            {
               if (Next(pBuf))
               {
                  // Fetch next set
                  if (!LazyRead(Next(pBuf),&pBuf))
                  {
                     _iErr = BPPT_IDX_ERR_SECTOR_SIZE;

                     TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                     
                     return false;
                  }
               }
               else
               {
                  break;
               }
            }
         }

         if (!Search(pBuf,pKey,&pFound))
         {
            *pValue = ValueOF(pFound);

            _pHandle->_pCurBuf = pBuf;
            _pHandle->_pCurKey = pFound;
            return true;
         }
         else
         {
            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;
// Don't report about mismatched key
//            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
            return false;
         }
      }
      else
      {
         if (!_pHandle->_bDuplicate)
         {
            if (Search(pBuf,pKey,&pFound) < 0)
            {
               if (!LazyRead(Child_LT(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
         }
         else
         {
            if (Search(pBuf,pKey,&pFound) <= 0)
            {
               if (!LazyRead(Child_LT(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return false;
               }
            }
         }
      }
   }
}

/* ******************************************************************** **
** @@ BPPTreeIndex::IncValue()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify : 
** @  Update :
** @  Notes  : !! Very special case if Value is Integer Counter !!
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

DWORD BPPTreeIndex::IncValue(const char* const pKey)
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return 0;
   }

   BPPT_INDEX_BUFFER*      pBuf   = &_pHandle->_Root;    // buffer
   char*             pFound = NULL;                // matched key

   // Find key, and return address
   #pragma warning (disable: 4127)    // conditional expression is constant                                    
   while (true)   
   {
      if (Leaf(pBuf))
      {
         if (_pHandle->_bDuplicate)
         {
            while (!Count(pBuf))
            {
               if (Next(pBuf))
               {
                  // Fetch next set
                  if (!LazyRead(Next(pBuf),&pBuf))
                  {
                     _iErr = BPPT_IDX_ERR_SECTOR_SIZE;

                     TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

                     return 0;
                  }
               }
               else
               {
                  break;
               }
            }
         }

         if (!Search(pBuf,pKey,&pFound))
         {
            ++(*(DWORD*)(pFound + _pHandle->_iKeySize)); 

            _pHandle->_pCurBuf = pBuf;
            _pHandle->_pCurKey = pFound;
            return *(DWORD*)(pFound + _pHandle->_iKeySize);
         }
         else
         {
            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;
// Don't report about mismatched key
//            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
            return 0;
         }
      }
      else
      {
         if (!_pHandle->_bDuplicate)
         {
            if (Search(pBuf,pKey,&pFound) < 0)
            {
               if (!LazyRead(Child_LT(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return 0;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return 0;
               }
            }
         }
         else
         {
            if (Search(pBuf,pKey,&pFound) <= 0)
            {
               if (!LazyRead(Child_LT(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return 0;
               }
            }
            else
            {
               if (!LazyRead(Child_GE(pFound),&pBuf))
               {
                  TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
                  return 0;
               }
            }
         }
      }
   }
}

/* ******************************************************************** **
** @@ BPPTreeIndex::FindFirst()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : 
** ******************************************************************** */

bool BPPTreeIndex::FindFirst
(
   char*                   pKey,    // first key in sequential set
   DWORD*                  pValue   // record address
)
{
   if (pValue)
   {
      *pValue = 0;
   }

   if (!_pHandle)
   {
      // Error !
      ASSERT(0);
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   BPPT_INDEX_BUFFER*      pBuf = &_pHandle->_Root;  // buffer

   while (!Leaf(pBuf))
   {
      if (!LazyRead(Child_LT(First(pBuf)),&pBuf))
      {
         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
         return false;
      }
   }

   if (!_pHandle->_bDuplicate)
   {
      if (!Count(pBuf))
      {
         _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;
// Don't LOG about duplicates !
//         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
         return false;
      }
   }
   else
   {
      if (!Count(pBuf))
      {
         _pHandle->_pCurBuf = pBuf;
         return FindNext(pKey,pValue);
      }
   }

   if (pKey)
   {
      memcpy(pKey,First(pBuf),_pHandle->_iKeySize);
   }

   if (pValue)
   {
      *pValue = ValueOF(First(pBuf));
   }

   _pHandle->_pCurBuf = pBuf;
   _pHandle->_pCurKey = First(pBuf);

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::FindLast()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

bool BPPTreeIndex::FindLast
(
   char*                   pKey,    // last key in sequential set
   DWORD*                  pValue   // record address
)
{
   if (pValue)
   {
      *pValue = 0;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   BPPT_INDEX_BUFFER*      pBuf = &_pHandle->_Root;

   while (!Leaf(pBuf))
   {
      if (!LazyRead(Child_GE(Last(pBuf)),&pBuf))
      {
         _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }
   }

   if (!_pHandle->_bDuplicate)
   {
      if (!Count(pBuf))
      {
         _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }
   }
   else
   {
      if (!Count(pBuf))
      {
         _pHandle->_pCurBuf = pBuf;
         return FindPrev(pKey,pValue);
      }
   }

   if (pKey)
   {
      memcpy(pKey,Last(pBuf),_pHandle->_iKeySize);
   }

   if (pValue)
   {
      *pValue = ValueOF(Last(pBuf));
   }
     
   _pHandle->_pCurBuf = pBuf;
   _pHandle->_pCurKey = Last(pBuf);

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::FindPrev()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

bool BPPTreeIndex::FindPrev
(
   char*             pKey,    // key found
   DWORD*            pValue   // record address
)
{
   if (pValue)
   {
      *pValue = 0;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   BPPT_INDEX_BUFFER*    pCurrent = _pHandle->_pCurBuf;     // buffer

   if (!pCurrent)
   {
      _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   char*    pPrevKey = NULL;    // previous key

   if (!_pHandle->_bDuplicate)
   {
      if (_pHandle->_pCurKey == First(pCurrent))
      {
         // current key is first key in leaf node
         if (Prev(pCurrent))
         {
            // fetch previous set
            if (!LazyRead(Prev(pCurrent),&pCurrent))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            pPrevKey = First(pCurrent) + KeysSize((Count(pCurrent) - 1));
         }
         else
         {
            // no more sets
            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

            return false;
         }
      }
      else
      {
         // bump to previous key
         pPrevKey = _pHandle->_pCurKey - KeysSize(1);
      }
   }
   else
   {
      if ((_pHandle->_pCurKey == First(pCurrent)) || !Count(pCurrent))
      {
         bool     bFound = false;

         while (Prev(pCurrent))
         {
            if (!LazyRead(Prev(pCurrent),&pCurrent))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            if (Count(pCurrent))
            {
               pPrevKey = Last(pCurrent);
               bFound   = true;
               break;
            }
         }

         if (!bFound)
         {
            // no more sets
            _pHandle->_pCurBuf = NULL;
            _pHandle->_pCurKey = NULL;

            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

            return false;
         }      
      }
      else
      {
         // bump to previous key
         pPrevKey = _pHandle->_pCurKey - KeysSize(1);
      }
   }

   if (pKey)
   {
      memcpy(pKey,pPrevKey,_pHandle->_iKeySize);
   }

   if (pValue)
   {
      *pValue = ValueOF(pPrevKey);
   }

   _pHandle->_pCurBuf = pCurrent;
   _pHandle->_pCurKey = pPrevKey;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::FindNext()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : ERR_OK            - operation successful
** @  Notes  : BPPT_IDX_ERR_KEY_NOT_FOUND - key not found
** ******************************************************************** */

bool BPPTreeIndex::FindNext
(
   char*             pKey,    // key found
   DWORD*            pValue   // record address
)
{
   if (pValue)
   {
      *pValue = 0;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   BPPT_INDEX_BUFFER*      pBuf = _pHandle->_pCurBuf;   

   if (!pBuf)
   {
      _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   char*    pNextKey = NULL;
   
   if (!_pHandle->_bDuplicate)
   {
      if (_pHandle->_pCurKey == Last(pBuf))
      {
         // current key is last key in leaf node
         if (Next(pBuf))
         {
            // fetch next set
            if (!LazyRead(Next(pBuf),&pBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            pNextKey = First(pBuf);
         }
         else
         {
            // no more sets
            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

            TRACE("File: %s, Line: %d, Err: [KEY_NOT_FOUND] %d\n",__FILE__,__LINE__,_iErr);

            return false;
         }
      }
      else
      {
         // bump to next key in the Buff
         pNextKey = _pHandle->_pCurKey + KeysSize(1);
      }
   }
   else
   {
      if (_pHandle->_pCurKey == Last(pBuf)  || !Count(pBuf))
      {
         bool     bFound = false;

         // current key is last key in leaf node
         while (Next(pBuf))
         {
            if (!LazyRead(Next(pBuf),&pBuf))
            {
               TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
               return false;
            }

            if (Count(pBuf))
            {
               pNextKey = First(pBuf);
               bFound = true;
               break;
            }
         }

         if (!bFound)
         {
            // no more sets
            _pHandle->_pCurBuf=NULL;
            _pHandle->_pCurKey=NULL;

            _iErr = BPPT_IDX_ERR_KEY_NOT_FOUND;

            TRACE("File: %s, Line: %d, Err: [KEY_NOT_FOUND] %d\n",__FILE__,__LINE__,_iErr);

            return false;
         }
      }
      else
      {
         // bump to next key in the Buff
         pNextKey = _pHandle->_pCurKey + KeysSize(1);
      }
   }

   if (pKey)
   {
      memcpy(pKey,pNextKey,_pHandle->_iKeySize);
   }

   if (pValue)
   {
      *pValue = ValueOF(pNextKey);
   }

   _pHandle->_pCurBuf = pBuf;
   _pHandle->_pCurKey = pNextKey;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::LazyRead()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

bool BPPTreeIndex::LazyRead
(
   DWORD                dwAdr,
   BPPT_INDEX_BUFFER**        pIdxBuf
)
{
   if (!pIdxBuf)
   {
      // Error !
      return false;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   // read data into buf
   int               iLenght = 0; 
   BPPT_INDEX_BUFFER*      pBuf    = NULL;

   if (!AssignBuf(dwAdr,&pBuf))
   {
      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
      return false;
   }

   if (!pBuf->_bValid)
   {
      iLenght = _pHandle->_iSectorSize;

      if (!dwAdr)
      {
         iLenght *= 3;         // root
      }

      SetFilePointerCUR(_pHandle->_hFile,dwAdr,FILE_BEGIN);

      if (!ReadBuffer(_pHandle->_hFile,pBuf->_pMemNode,iLenght))
      {
         _iErr = BPPT_IDX_ERR_IO;

         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

         return false;
      }

      pBuf->_bModified = false;
      pBuf->_bValid    = true;

      ++_StatInfo._iDiskReads;
   }

   *pIdxBuf = pBuf;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::LazyWrite()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : write buf to disk
** ******************************************************************** */

void BPPTreeIndex::LazyWrite(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return;
   }

   pBuf->_bValid    = true;
   pBuf->_bModified = true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Flush()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Flush buffer to disk
** ******************************************************************** */

bool BPPTreeIndex::Flush(BPPT_INDEX_BUFFER* pBuf)
{
   if (!pBuf)
   {
      // Error !
      return false;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   int   iSize = _pHandle->_iSectorSize;  // number of bytes to write

   if (!pBuf->_dwDiskAdr)
   {
      iSize *= 3;        // root
   }

   SetFilePointerCUR(_pHandle->_hFile,pBuf->_dwDiskAdr,FILE_BEGIN);

   if (!WriteBuffer(_pHandle->_hFile,pBuf->_pMemNode,iSize))
   {  
      _iErr = BPPT_IDX_ERR_IO;

      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);

      return false;
   }

   ++_StatInfo._iDiskWrites;
   pBuf->_bModified = false;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::FlushAll()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

void BPPTreeIndex::Flush()
{
   FlushAll();
}

/* ******************************************************************** **
** @@ BPPTreeIndex::FlushAll()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

bool BPPTreeIndex::FlushAll()
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   if (_pHandle->_Root._bModified)
   {
      if (!Flush(&_pHandle->_Root))
      {
         #ifdef _MFC_VER
         TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
         #endif
         return false;
      }
   }

   BPPT_INDEX_BUFFER*      pBuf = _pHandle->_Cache._pNext;

   // Cache Dump
   while (pBuf != &_pHandle->_Cache)
   {
      if (pBuf->_bModified)
      {
         if (!Flush(pBuf))
         {
            #ifdef _MFC_VER
            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
            #endif
            return false;
         }
      }

      pBuf = pBuf->_pNext;
   }

   _pHandle->_bFlushed = true;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Allocate()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

DWORD BPPTreeIndex::Allocate()
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   DWORD   dwAdr = _pHandle->_dwNextFreeAdr;

   _pHandle->_dwNextFreeAdr += _pHandle->_iSectorSize;

   return dwAdr;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::AssignBuf()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

bool BPPTreeIndex::AssignBuf(DWORD dwAdr,BPPT_INDEX_BUFFER** pIdxBuf)
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   // assign buf to adr
   if (!dwAdr)
   {
      *pIdxBuf = &_pHandle->_Root;
      return true;
   }

   // search for buf with matching adr
   BPPT_INDEX_BUFFER*    pBuf = _pHandle->_Cache._pNext;

   // Fetch from Cache
   while (pBuf->_pNext != &_pHandle->_Cache)
   {
      if (pBuf->_bValid && (pBuf->_dwDiskAdr == dwAdr))
      {
         break;
      }
               
      pBuf = pBuf->_pNext;
   }

   // either buf points to a match, or it's last one in list (LRR)
   if (pBuf->_bValid)
   {
      if (pBuf->_dwDiskAdr != dwAdr)
      {
         if (pBuf->_bModified)
         {
            if (!Flush(pBuf))
            {
               #ifdef _MFC_VER
               TRACE("File: %s, Line: %d, Errcode: %d",__FILE__,__LINE__,_iErr);
               #endif
               return false;
            }
         }

         pBuf->_dwDiskAdr = dwAdr;
         pBuf->_bValid    = false;
      }
   }
   else
   {
      pBuf->_dwDiskAdr = dwAdr;
   }

   // remove from current position and place at front of list
   pBuf->_pNext->_pPrev = pBuf->_pPrev;
   pBuf->_pPrev->_pNext = pBuf->_pNext;

   pBuf->_pNext = _pHandle->_Cache._pNext;
   pBuf->_pPrev = &_pHandle->_Cache;

   pBuf->_pNext->_pPrev = pBuf;
   pBuf->_pPrev->_pNext = pBuf;

   *pIdxBuf = pBuf;

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Search()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : BPPT_IDX_COND_EQ:   key = pFound
** @  Notes  : BPPT_IDX_COND_LT:   key < pFound
** @  Notes  : BPPT_IDX_COND_GT:   key > pFound
** ******************************************************************** */

int BPPTreeIndex::Search
(                                        
   BPPT_INDEX_BUFFER*            pBuf,       // Pointer to node
   const char* const       pKey,       // Key to find
   char**                  pFound      // Pointer to keyType info
)
{
   if (!pBuf)
   {
      // Error !
      return BPPT_IDX_COND_EQ;
   }

   if (!pKey)
   {
      // Error !
      return BPPT_IDX_COND_EQ;
   }

   if (!pFound)
   {
      // Error !
      return BPPT_IDX_COND_EQ;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return BPPT_IDX_COND_EQ;
   }

   int   iFound    = BPPT_IDX_COND_EQ;            // Condition code
   int   iLower    = 0;                // Lower-bound of binary search
   int   iUpper    = Count(pBuf) - 1;  // Upper-bound of binary search
   int   iMidPoint = 0;

   while (iLower <= iUpper)
   {
      iMidPoint = (iLower + iUpper) >> 1;  // Midpoint of search

      *pFound = First(pBuf) + KeysSize(iMidPoint);
      
      iFound = _pHandle->_pCompare(pKey,*pFound);

      if (iFound < 0)
      {
         iUpper = iMidPoint - 1;    // key less than key[m]
      }
      else if (iFound > 0)
      {
         iLower = iMidPoint + 1;    // key greater than key[m]
      }
      else
      {
         if (!_pHandle->_bDuplicate)
         {
            return iFound;
         }
         else
         {
            break;                  // keys match
         }
      }
   }

   if (!Count(pBuf))                // empty list
   {
      *pFound = First(pBuf);
      return BPPT_IDX_COND_LT;
   }

   if (_pHandle->_bDuplicate)
   {
      if (iFound)
      {
         return iFound;
      }

      while (iMidPoint > 0)
      {
         --iMidPoint;

         *pFound = First(pBuf) + KeysSize(iMidPoint);
      
         iFound = _pHandle->_pCompare(pKey,*pFound);
      
         if (iFound)
         {
            ++iMidPoint;

            *pFound = First(pBuf) + KeysSize(iMidPoint);
            iFound  = _pHandle->_pCompare(pKey,*pFound);

            break;
         }
      }
   }

   return iFound;  // Didn't find key
}

/* ******************************************************************** **
** @@ BPPTreeIndex::ScatterRoot()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Scatter GatherBuf to Root
** ******************************************************************** */

void BPPTreeIndex::ScatterRoot()
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return;
   }

   BPPT_INDEX_BUFFER*      pRoot      = &_pHandle->_Root;
   BPPT_INDEX_BUFFER*      pGatherBuf = &_pHandle->_GatherBuf;

   memcpy(First(pRoot),First(pGatherBuf),KeysSize(Count(pGatherBuf)));

   SetChild_LT(First(pRoot),Child_LT(First(pGatherBuf)));
   SetCount(pRoot,Count(pGatherBuf));
   SetLeaf(pRoot,Leaf(pGatherBuf));
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Scatter()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : pParentBuf - parent buffer of gathered keys
** @  Notes  : pParentKey - where we insert a key if needed in parent
** @  Notes  : iTempMax   - number of supplied tmps
** @  Notes  : pTempArr   - array of tmp's to be used for scattering / array of tmp's used for scattering
** ******************************************************************** */

bool BPPTreeIndex::Scatter
(
   BPPT_INDEX_BUFFER*            pParentBuf,
   char*                   pParentKey,
   int                     iTempMax,
   BPPT_INDEX_BUFFER**           pTempArr
)
{
   if (!pParentBuf)
   {
      // Error !
      return false;
   }

   if (!pParentKey)
   {
      // Error !
      return false;
   }

   if (!pTempArr)
   {
      // Error !
      return false;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   // Scatter GatherBuf to tmps, placing 3/4 max in each tmp
   BPPT_INDEX_BUFFER*      pGatherBuf = &_pHandle->_GatherBuf;    // gather buf
   char*             pGatherKey = First(pGatherBuf);    // gather buf key

   int   iCnt = Count(pGatherBuf);

   // determine number of tmps to use
   int   iUsed = iTempMax;    // number of tmp's used

   int k0Min;                  // min #keys that can be mapped to tmp[0]
   int k0Max;                  // max #keys that can be mapped to tmp[0]
   int knMin;                  // min #keys that can be mapped to tmp[1..3]
   int knMax;                  // max #keys that can be mapped to tmp[1..3]

   // determine limits
   if (Leaf(pGatherBuf))
   {
      // minus 1 to allow for insertion
      k0Max= _pHandle->_dwMaxKeyCnt - 1;
      knMax= _pHandle->_dwMaxKeyCnt - 1;

      // plus 1 to allow for deletion
      k0Min= (_pHandle->_dwMaxKeyCnt >> 1) + 1;
      knMin= (_pHandle->_dwMaxKeyCnt >> 1) + 1;
   }
   else  // can hold an extra GatherBuf key as it's translated to a LT pointer
   {
      // minus 1 to allow for insertion
      k0Max = _pHandle->_dwMaxKeyCnt - 1;
      knMax = _pHandle->_dwMaxKeyCnt;

      // plus 1 to allow for deletion
      k0Min = (_pHandle->_dwMaxKeyCnt >> 1) + 1;
      knMin = ((_pHandle->_dwMaxKeyCnt + 1) >> 1) + 1;
   }

   // calculate iUsed, number of tmps to use
   #pragma warning (disable: 4127)    // conditional expression is constant                                    
   while (true)
   {
      if (!iUsed || (iCnt > (k0Max + (iUsed - 1) * knMax)))
      {
         // add a buffer
         if (!AssignBuf(Allocate(),&pTempArr[iUsed]))
         {
            #ifdef _MFC_VER
            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
            #endif
            return false;
         }

         // update sequential links
         if (Leaf(pGatherBuf))
         {
            // adjust sequential links
            if (!iUsed)
            {
               // no tmps supplied when splitting root for first time
               SetPrev(pTempArr[0],0);
               SetNext(pTempArr[0],0);
            }
            else
            {
               SetPrev(pTempArr[iUsed],pTempArr[iUsed - 1]->_dwDiskAdr);
               SetNext(pTempArr[iUsed],Next(pTempArr[iUsed - 1]));
               SetNext(pTempArr[iUsed - 1],pTempArr[iUsed]->_dwDiskAdr);
            }
         }

         ++iUsed;
         ++_StatInfo._iNodesIns;
      }
      else if (iUsed > 1 && iCnt < (k0Min + (iUsed - 1) * knMin))
      {
         // del a buffer
         --iUsed;

         SetNext(pTempArr[iUsed - 1],Next(pTempArr[iUsed]));      // ??????????

         ++_StatInfo._iNodesDel;
      }
      else
      {
         break;
      }
   }

   // establish count for each tmp used
   int   iBase  = iCnt / iUsed;     // base count distributed to tmps
   int   iExtra = iCnt % iUsed;     // extra counts

   for (int ii = 0; ii < iUsed; ++ii)
   {
      int   iStart = iBase;

      // distribute extras, one at a time
      // don't do to 1st node, as it may be internal and can't hold it
      if (iExtra && ii)
      {
         ++iStart;
         --iExtra;
      }

      SetCount(pTempArr[ii],iStart);
   }

   // Update Sequential Links and Parent
   if (iUsed != iTempMax)
   {
      // Link Last Node to Next
      if (Leaf(pGatherBuf) && Next(pTempArr[iUsed - 1]))
      {
         BPPT_INDEX_BUFFER*   buf = NULL;

         if (!LazyRead(Next(pTempArr[iUsed - 1]),&buf))
         {
            #ifdef _MFC_VER
            TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
            #endif
            return false;
         }

         SetPrev(buf,pTempArr[iUsed - 1]->_dwDiskAdr);

         LazyWrite(buf);
      }

      // shift keys in parent
      int   iShiftWidth = KeysSize(iUsed - iTempMax);   // shift width

      int   iLength = 0;   // length of remainder of buf

      if (iShiftWidth < 0)
      {
         iLength = KeysSize(Count(pParentBuf)) - (pParentKey - First(pParentBuf)) + iShiftWidth;
         memmove(pParentKey,pParentKey - iShiftWidth,iLength);
      }
      else
      {
         iLength = KeysSize(Count(pParentBuf)) - (pParentKey - First(pParentBuf));
         memmove(pParentKey + iShiftWidth,pParentKey,iLength);
      }

      // don't count LT buffer for empty parent
      if (Count(pParentBuf))
      {
         Inc(pParentBuf,iUsed - iTempMax);
      }
      else
      {
         Inc(pParentBuf,iUsed - iTempMax - 1);
      }
   }

   // distribute keys to children
   for (ii = 0; ii < iUsed; ++ii)
   {
      // update LT pointer and parent nodes
      if (Leaf(pGatherBuf))
      {
         // update LT, tmp[i]
         SetChild_LT(First(pTempArr[ii]),0);

         // update parent
         if (!ii)
         {
            SetChild_LT(pParentKey,pTempArr[ii]->_dwDiskAdr);
         }
         else
         {
            memcpy(pParentKey,pGatherKey,KeysSize(1));

            SetChild_GE(pParentKey,pTempArr[ii]->_dwDiskAdr);
            pParentKey += KeysSize(1);
         }
      }
      else
      {
         if (!ii)
         {
            // update LT, tmp[0]
            SetChild_LT(First(pTempArr[ii]),Child_LT(pGatherKey));

            // update LT, parent
            SetChild_LT(pParentKey,pTempArr[ii]->_dwDiskAdr);
         }
         else
         {
            // update LT, tmp[i]
            SetChild_LT(First(pTempArr[ii]),Child_GE(pGatherKey));

            // update parent key
            memcpy(pParentKey,pGatherKey,KeysSize(1));

            SetChild_GE(pParentKey,pTempArr[ii]->_dwDiskAdr);

            pGatherKey += KeysSize(1);
            pParentKey += KeysSize(1);

            Dec(pTempArr[ii]);
         }
      }

      // install keys, tmp[i]
      memcpy(First(pTempArr[ii]),pGatherKey,KeysSize(Count(pTempArr[ii])));

      SetLeaf(pTempArr[ii],Leaf(pGatherBuf));

      pGatherKey += KeysSize(Count(pTempArr[ii]));
   }

   SetLeaf(pParentBuf,false);

   // write modified nodes
   LazyWrite(pParentBuf);

   for (ii = 0; ii < iUsed; ++ii)
   {
      LazyWrite(pTempArr[ii]);
   }

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::GatherRoot()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : gather root to gbuf
** ******************************************************************** */

void BPPTreeIndex::GatherRoot()
{
   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return;
   }

   BPPT_INDEX_BUFFER*      pRoot      = &_pHandle->_Root;
   BPPT_INDEX_BUFFER*      pGatherBuf = &_pHandle->_GatherBuf;

   memcpy(Ptr(pGatherBuf),pRoot->_pMemNode,3 * _pHandle->_iSectorSize);

   SetLeaf(pGatherBuf,Leaf(pRoot));
   SetCount(pRoot,0);
}

/* ******************************************************************** **
** @@ BPPTreeIndex::Gather()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : Gather 3 buffers to gbuf.  Setup for subsequent scatter by
** @  Notes  : doing the following:
** @  Notes  : - setup tmp buffer array for scattered buffers
** @  Notes  : - adjust pkey to point to first key of 3 buffers
** @  Notes  : pbuf   - parent buffer
** @  Notes  : pkey   - pointer to match key in parent
** @  Notes  : tmp    - buffers to use for scatter
** @  Notes  : pkey   - pointer to match key in parent
** @  Notes  : ERR_OK - operation successful
** ******************************************************************** */

bool BPPTreeIndex::Gather(BPPT_INDEX_BUFFER* pIdxBuf,char** pKey,BPPT_INDEX_BUFFER** pTmpBuf)
{
   if (!pIdxBuf)
   {
      // Error !
      return false;
   }

   if (!pKey)
   {
      // Error !
      return false;
   }

   if (!pTmpBuf)
   {
      // Error !
      return false;
   }

   if (!_pHandle)
   {
      // Error !
      _iErr = BPPT_IDX_ERR_HANDLE_NULL_PTR;
      return false;
   }

   // find 3 adjacent buffers
   if (*pKey == Last(pIdxBuf))
   {
      *pKey -= KeysSize(1);
   }

   if (!LazyRead(Child_LT(*pKey),&pTmpBuf[0]))
   {
      #ifdef _MFC_VER
      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
      #endif
      return false;
   }

   if (!LazyRead(Child_GE(*pKey),&pTmpBuf[1]))
   {
      #ifdef _MFC_VER
      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
      #endif
      return false;
   }

   if (!LazyRead(Child_GE(*pKey + KeysSize(1)),&pTmpBuf[2]))
   {
      #ifdef _MFC_VER
      TRACE("File: %s, Line: %d, Err: %d\n",__FILE__,__LINE__,_iErr);
      #endif
      return false;
   }

   // gather nodes to gbuf
   BPPT_INDEX_BUFFER*      pGBuf = &_pHandle->_GatherBuf;
   char*             pGKey = First(pGBuf);

   // tmp[0]
   SetChild_LT(pGKey,Child_LT(First(pTmpBuf[0])));

   memcpy(pGKey,First(pTmpBuf[0]),KeysSize(Count(pTmpBuf[0])));

   pGKey += KeysSize(Count(pTmpBuf[0]));

   SetCount(pGBuf,Count(pTmpBuf[0]));

   // tmp[1]
   if (!Leaf(pTmpBuf[1]))
   {
      memcpy(pGKey,*pKey,KeysSize(1));

      SetChild_GE(pGKey,Child_LT(First(pTmpBuf[1])));

      Inc(pGBuf);

      pGKey += KeysSize(1);
   }

   memcpy(pGKey,First(pTmpBuf[1]),KeysSize(Count(pTmpBuf[1])));

   pGKey += KeysSize(Count(pTmpBuf[1]));

   Inc(pGBuf,Count(pTmpBuf[1]));

   // tmp[2]
   if (!Leaf(pTmpBuf[2]))
   {
      memcpy(pGKey,*pKey + KeysSize(1),KeysSize(1));

      SetChild_GE(pGKey,Child_LT(First(pTmpBuf[2])));

      Inc(pGBuf);

      pGKey += KeysSize(1);
   }

   memcpy(pGKey,First(pTmpBuf[2]),KeysSize(Count(pTmpBuf[2])));

   Inc(pGBuf,Count(pTmpBuf[2]));

   SetLeaf(pGBuf,Leaf(pTmpBuf[0]));

   return true;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::CountKeyStat()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : 
** ******************************************************************** */

int BPPTreeIndex::CountKeyStat() 
{ 
   return _StatInfo._iKeysIns - _StatInfo._iKeysDel; 
}    

/* ******************************************************************** **
** @@ BPPTreeIndex::Statistics()
** @  Copyrt : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.html
** @  Author : Jan Jannink * http://home.od.ua/~relayer/algo/data/btree/s_btr.txt
** @  Modify :
** @  Update :
** @  Notes  : 
** ******************************************************************** */

const BPPT_STAT_INFO& BPPTreeIndex::Statistics() const 
{ 
   return _StatInfo; 
}

/* ******************************************************************** **
** @@ BPPTreeIndex::DescribeError()
** @  Copyrt : 
** @  Author :
** @  Modify : 
** @  Update :
** @  Notes  : 
** ******************************************************************** */

int BPPTreeIndex::GetLastErr() const
{
   return _iErr;
}

/* ******************************************************************** **
** @@ BPPTreeIndex::DescribeError()
** @  Copyrt : 
** @  Author :
** @  Modify : 
** @  Update :
** @  Notes  : 
** ******************************************************************** */

const char* const BPPTreeIndex::DescribeError()
{
   if (!_iErr)
   {
      return "";
   }

   switch (_iErr)
   {
      default:
      {
         return "";
      }
      case BPPT_IDX_ERR_KEY_NOT_FOUND:
      {
         return "Key not found.";
      }
      case BPPT_IDX_ERR_DUP_KEYS:
      {
         return "Dup keys.";
      }
      case BPPT_IDX_ERR_SECTOR_SIZE:
      {
         return "Err sector size.";
      }
      case BPPT_IDX_ERR_FILE_NOT_OPEN:
      {
         return "File is not open.";
      }
      case BPPT_IDX_ERR_FILE_EXISTS:
      {
         return "File is not exists.";
      }
      case BPPT_IDX_ERR_IO:
      {
         return "I/O error.";
      }
      case BPPT_IDX_ERR_MEMORY:
      {
         return "Memory error.";
      }
      case BPPT_IDX_ERR_CORRUPTED:
      {
         return "Index corrupt.";
      }
   }
}

/* ******************************************************************** **
** End of File
** ******************************************************************** */
