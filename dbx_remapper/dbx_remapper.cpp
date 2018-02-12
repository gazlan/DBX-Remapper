/* ******************************************************************** **
** @@ DBX Remapper
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Note   :
** ******************************************************************** */

/* ******************************************************************** **
**                uses pre-compiled headers
** ******************************************************************** */

#include "stdafx.h"

#include <stdio.h>
#include <limits.h>
#include <time.h>

#include "..\shared\xlat_tables.h"
#include "..\shared\xlat.h"
#include "..\shared\text.h"
#include "..\shared\file.h"
#include "..\shared\file_walker.h"
#include "..\shared\mmf.h"
#include "..\shared\timestamp.h"
#include "..\shared\vector.h"
#include "..\shared\vector_sorted.h"
#include "..\shared\db_dbx.h"
#include "..\shared\hash_murmur3.h"
#include "..\shared\map_bppt_jannink.h"

#ifdef NDEBUG
#pragma optimize("gsy",on)
#pragma comment(linker,"/FILEALIGN:512 /MERGE:.rdata=.text /MERGE:.data=.text /SECTION:.text,EWR /IGNORE:4078")
#endif

#ifdef _DEBUG
#define new DEBUG_NEW
#undef THIS_FILE
static char THIS_FILE[] = __FILE__;
#endif

/* ******************************************************************** **
** @@                   internal defines
** ******************************************************************** */

#ifndef QWORD
typedef unsigned __int64   QWORD;
#endif

#define MAX_RECORD_SIZE                         (128)
#define MAX_DUPS_COUNT                          (1024) // !!

static CString    _sTable10_RU          = _T("");
static CString    _sTable10_RU_DBF      = _T("");
static CString    _sTable10_RU_DBV      = _T("");

static CString    _sTable10_RU_NEW      = _T("");
static CString    _sTable10_RU_NEW_DBF  = _T("");
// static CString    _sTable10_RU_NEW_DBV  = _T("");

static CString    _sTable10_RU_LINK     = _T("");
static CString    _sTable10_RU_LINK_DBF = _T("");
static CString    _sTable10_RU_LINK_DBV = _T("");

static CString    _sTable10_RU_MAP      = _T("");
static CString    _sTable10_RU_MAP_DBF  = _T("");

enum DBV_FLAGS
{
   DBV_FLAG_NONE      = 0x0000,
   DBV_FLAG_TRANLATED = 0x0001,
   DBV_FLAG_VERIFIED  = 0x0002,
   DBV_FLAG_MARKED    = 0x0004,
   DBV_FLAG_COMMENTED = 0x0008,
   DBV_FLAG_CHANGED   = 0x0010,
   DBV_FLAG_LINKED    = 0x0020,
   DBV_FLAG_MAIN      = 0x0040, 
   DBV_FLAG_MIRROR    = 0x0080, 
   DBV_FLAG_SINGLE    = 0x0100 
};
 
struct DBV_RECORD
{
   DWORD       _dwRecNum;
   DWORD       _dwIndexFrom;
   DWORD       _dwIndexTo;
   DWORD       _dwLink;
   DWORD       _dwTextSize;
   char*       _pszText;
   DWORD       _dwCommentSize;
   char*       _pszComment;
   DWORD       _dwArraySize;
   DWORD*      _pArray;
   WORD        _wFlags;
   bool        _bLinked;
   int         _iLinkCnt;
};

/* ******************************************************************** **
** @@                   internal prototypes
** ******************************************************************** */

/* ******************************************************************** **
** @@                   external global variables
** ******************************************************************** */

extern DWORD   dwKeepError = 0;

/* ******************************************************************** **
** @@                   static global variables
** ******************************************************************** */

static DWORD         _dwGranulation = 3; // 2 Power: 0, 2, 3, 4

static char          _pRecord[MAX_RECORD_SIZE];

static DBX_TABLE_INFO      _InfoSrc;
static DBX_TABLE_INFO      _InfoNew;
static DBX_TABLE_INFO      _InfoLink;
static DBX_TABLE_INFO      _InfoMap;

static SortedVector*       _pVectSrc  = NULL;  
static SortedVector*       _pVectLink = NULL;  

#define VECTOR_INITIAL_SIZE      (8192) 
#define VECTOR_DELTA             (1024) 

static BYTE          _pDummy[MAX_PATH];

static DWORD         _pArray[MAX_DUPS_COUNT];

static DWORD         _dwPageSize3 = 0;

/* ******************************************************************** **
** @@                   real code
** ******************************************************************** */

/* ******************************************************************** **
** @@ CMP_IndexFrom()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

inline int CMP_IndexFrom(const void** const pKey1,const void** const pKey2)
{
   DBV_RECORD*    p1 = *(DBV_RECORD**)pKey1;
   DBV_RECORD*    p2 = *(DBV_RECORD**)pKey2;

   if (p1->_dwIndexFrom > p2->_dwIndexFrom)
   {
      return 1;
   }
   else if (p1->_dwIndexFrom < p2->_dwIndexFrom)
   {
      return -1;
   }
   else
   {
      return 0;
   }
}

/* ******************************************************************** **
** @@ CMP_IndexTo()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

inline int CMP_IndexTo(const void** pKey1,const void** pKey2)
{
   DBV_RECORD*    p1 = *(DBV_RECORD**)pKey1;
   DBV_RECORD*    p2 = *(DBV_RECORD**)pKey2;

   if (p1->_dwIndexTo > p2->_dwIndexTo)
   {
      return 1;
   }
   else if (p1->_dwIndexTo < p2->_dwIndexTo)
   {
      return -1;
   }
   else
   {
      return 0;
   }
}

/* ******************************************************************** **
** @@ CMP_Link()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

inline int CMP_Link(const void** pKey1,const void** pKey2)
{
   DBV_RECORD*    p1 = *(DBV_RECORD**)pKey1;
   DBV_RECORD*    p2 = *(DBV_RECORD**)pKey2;

   if (p1->_dwLink > p2->_dwLink)
   {
      return 1;
   }
   else if (p1->_dwLink < p2->_dwLink)
   {
      return -1;
   }
   else
   {
      return 0;
   }
}

/* ******************************************************************** **
** @@ Load()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Load()
{
   DBX*     pDBX = new DBX;

   DBX_TABLE*     pDbSrc = pDBX->OpenTable
   (
      (LPCTSTR)_sTable10_RU,
      (LPCTSTR)_sTable10_RU_DBF,
      (LPCTSTR)_sTable10_RU_DBV,
      DBX_OM_READ_ONLY,
      DBX_OM_READ_ONLY,
      DBX_FM_FLUSH_NEVER,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pDbSrc)
   {
      // Error !
      ASSERT(0);
      return;
   }

   DWORD ii = 0;

   DWORD    dwRecCnt10 = pDbSrc->GetRecCnt();

   ASSERT(dwRecCnt10);

   MMF      _mmf10;

   _mmf10.OpenReadOnly((LPCTSTR)_sTable10_RU_DBV);

   BYTE*    pBuf10 = _mmf10.Buffer();

   ASSERT(pBuf10);

   _pVectSrc = new SortedVector;

   _pVectSrc->Resize(VECTOR_INITIAL_SIZE);  
   _pVectSrc->Delta(VECTOR_DELTA);  
   _pVectSrc->SetSorter(CMP_IndexFrom);  

   for (ii = 1; ii <= dwRecCnt10; ++ii)
   {
      DBV_RECORD*    p10 = new DBV_RECORD;

      memset(p10,0,sizeof(DBV_RECORD));

      const BYTE* const    pRecord = pDbSrc->Go(ii);

      ASSERT(pRecord);

      DBX_COLUMN*    pIndexFrom = pDbSrc->GetColumn("INDEX FROM");
      DBX_COLUMN*    pText      = pDbSrc->GetColumn("TEXT");
      DBX_COLUMN*    pComment   = pDbSrc->GetColumn("COMMENT");
      DBX_COLUMN*    pArray     = pDbSrc->GetColumn("ARRAY");
      DBX_COLUMN*    pFlags     = pDbSrc->GetColumn("FLAGS");

      ASSERT(pIndexFrom);
      ASSERT(pText);
      ASSERT(pComment);
      ASSERT(pArray);
      ASSERT(pFlags);

      DWORD    dwIndexFrom = *(DWORD*)pIndexFrom->Get(pRecord);
      DWORD    dwText      = *(DWORD*)pText->     Get(pRecord);
      DWORD    dwComment   = *(DWORD*)pComment->  Get(pRecord);
      DWORD    dwArray     = *(DWORD*)pArray->    Get(pRecord);

      BYTE     byFlags = *(BYTE*)pFlags->Get(pRecord);

      ASSERT(dwText);
      ASSERT(!(dwText & 0x07));
      
      ASSERT(!(dwComment & 0x07));
      ASSERT(!(dwArray   & 0x07));

      p10->_dwIndexFrom = dwIndexFrom;

      // Text
      p10->_dwTextSize = *(DWORD*)(pBuf10 + dwText);

      ASSERT(p10->_dwTextSize);

      p10->_pszText = new char[p10->_dwTextSize];

      memcpy(p10->_pszText,pBuf10 + dwText + sizeof(DWORD),p10->_dwTextSize);

      // Comment
      if (dwComment)
      {
         p10->_dwCommentSize = *(DWORD*)(pBuf10 + dwComment);

         ASSERT(p10->_dwCommentSize);

         p10->_pszComment = new char[p10->_dwCommentSize];

         memcpy(p10->_pszComment,pBuf10 + dwComment + sizeof(DWORD),p10->_dwCommentSize);

         if (p10->_pszComment && *p10->_pszComment)
         {
            byFlags |= DBV_FLAG_COMMENTED;
         }
      }

      // Array
      if (dwArray)
      {
         p10->_dwArraySize = *(DWORD*)(pBuf10 + dwArray);

         ASSERT(p10->_dwArraySize);
         ASSERT(!(p10->_dwArraySize & 0x03));

         p10->_pArray = new DWORD[p10->_dwArraySize >> 2]; // In DWORDS !

         memcpy(p10->_pArray,pBuf10 + dwArray + sizeof(DWORD),p10->_dwArraySize);

         if (p10->_pArray)
         {
            byFlags |= DBV_FLAG_LINKED;
         }
      }

      // Flags
      p10->_wFlags = byFlags;

      p10->_dwRecNum = ii;

      if (_pVectSrc->Insert(p10) == -1)
      {
         // Error !
         ASSERT(0);
         delete p10;
         p10 = NULL;
      }
   }

   _mmf10.Close();

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ AppendLink()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static int AppendLink(const DBV_RECORD* const pRec,int iLinkCnt)
{
   DBV_RECORD*    pEntry = new DBV_RECORD;

   memset(pEntry,0,sizeof(DBV_RECORD));

   pEntry->_dwRecNum    = pRec->_dwRecNum;
   pEntry->_dwIndexFrom = pRec->_dwIndexFrom;
   pEntry->_dwIndexTo   = pRec->_dwIndexTo;

   pEntry->_dwTextSize = pRec->_dwTextSize;
   
   if (pEntry->_dwTextSize)
   {
      pEntry->_pszText = new char[pEntry->_dwTextSize + 1];
    
      strcpy(pEntry->_pszText,pRec->_pszText);
   }

   pEntry->_dwCommentSize = pRec->_dwCommentSize;

   if (pEntry->_dwCommentSize)
   {
      pEntry->_pszComment = new char[pEntry->_dwCommentSize + 1];
    
      strcpy(pEntry->_pszComment,pRec->_pszComment);

      pEntry->_wFlags |= DBV_FLAG_COMMENTED;

      pEntry->_iLinkCnt = iLinkCnt;
   }

   if (_pVectLink->Insert(pEntry) == -1)
   {
      // Error !
      ASSERT(0);
      delete pEntry;
      pEntry = NULL;  
   }

   int   Idx = 0;

   DBV_RECORD*    pFound = (DBV_RECORD*)_pVectLink->Search(pEntry,&Idx);

   if (pFound)
   {
      return Idx + 1;   // One based !
   }
   
   ASSERT(0);
   return 0;
}

/* ******************************************************************** **
** @@ Reduce()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Reduce()
{
   _pVectLink = new SortedVector;

   _pVectLink->Resize(VECTOR_INITIAL_SIZE);  
   _pVectLink->Delta(VECTOR_DELTA);  
   _pVectLink->SetSorter(CMP_IndexFrom);  

   int   iCnt10 = _pVectSrc->Count();

   // Should be int !
   for (int ii = (iCnt10 - 1); ii >= 0; --ii)
   {
      DBV_RECORD*    p10 = (DBV_RECORD*)_pVectSrc->At(ii);

      if (p10 && (p10->_wFlags & DBV_FLAG_LINKED) && p10->_dwArraySize)
      {
         ASSERT(!(p10->_dwArraySize & 0x02));

         int   iItemCnt = p10->_dwArraySize / sizeof(DWORD);

         if (!iItemCnt)
         {
            // Already linked !
            continue;
         }

         memcpy(_pArray,p10->_pArray,p10->_dwArraySize);

         delete[] p10->_pArray;
         p10->_pArray = NULL;
         
         p10->_dwArraySize = 0;

         DWORD    dwLink = AppendLink(p10,iItemCnt);

         ASSERT(dwLink);

         // Main
         p10->_dwLink  = dwLink;
         p10->_bLinked = true;
         p10->_wFlags  = DBV_FLAG_MAIN | DBV_FLAG_LINKED;

         // Reduce ALL
         for (int kk = 0; kk < iItemCnt; ++kk)
         {  
            DBV_RECORD*    pCur = (DBV_RECORD*)_pVectSrc->At(kk);

            if (pCur && !pCur->_bLinked)
            {
               if (pCur->_pszText)
               {
                  delete[] pCur->_pszText;
                  pCur->_pszText = NULL; 
                  pCur->_dwTextSize = 0; 
               }

               if (pCur->_pszComment)
               {
                  delete[] pCur->_pszComment;
                  pCur->_pszComment = NULL; 
                  pCur->_dwCommentSize = 0; 
               }

               if (pCur->_pArray)
               {
                  delete[] pCur->_pArray;
                  pCur->_pArray = NULL; 
                  pCur->_dwArraySize = 0; 
               }  

               // Mirror                              
               pCur->_dwLink  = dwLink;
               pCur->_bLinked = true; 
               pCur->_wFlags  = DBV_FLAG_MIRROR | DBV_FLAG_LINKED;
            }
         }
      }
   }
}

/* ******************************************************************** **
** @@ CopySingles()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void CopySingles()
{
   int   iCnt10 = _pVectSrc->Count();

   // Should be int !
   for (int ii = (iCnt10 - 1); ii >= 0; --ii)
   {
      DBV_RECORD*    p10 = (DBV_RECORD*)_pVectSrc->At(ii);

      if (p10 && !p10->_bLinked)
      {
         DWORD    dwLink = AppendLink(p10,0);

         ASSERT(dwLink);

         if (p10->_pszText)
         {
            delete[] p10->_pszText;
            p10->_pszText = NULL; 
            p10->_dwTextSize = 0; 
         }

         if (p10->_pszComment)
         {
            delete[] p10->_pszComment;
            p10->_pszComment = NULL; 
            p10->_dwCommentSize = 0; 
         }

         p10->_dwLink  = dwLink;
         p10->_bLinked = true; 
         p10->_wFlags  = DBV_FLAG_SINGLE | DBV_FLAG_LINKED;
      }
   }
}

/* ******************************************************************** **
** @@ Cleanup()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Cleanup()
{
   int ii = 0;

   int   iCnt10 = _pVectSrc->Count();

   // Should be int !
   for (ii = (iCnt10 - 1); ii >= 0; --ii)
   {
      DBV_RECORD*    p10 = (DBV_RECORD*)_pVectSrc->At(ii);

      if (p10)
      {
         if (p10->_pszText)
         {
            delete[] p10->_pszText;
            p10->_pszText = NULL; 
         }

         if (p10->_pszComment)
         {
            delete[] p10->_pszComment;
            p10->_pszComment = NULL;
         }

         if (p10->_pArray)
         {
            delete[] p10->_pArray;
            p10->_pArray = NULL;
         }

         delete p10;
         p10 = NULL;
      }
   }

   if (_pVectSrc)
   {
      delete _pVectSrc;
      _pVectSrc = NULL;
   }

   int   iCntLnk = _pVectLink->Count();

   // Should be int !
   for (ii = (iCntLnk - 1); ii >= 0; --ii)
   {
      DBV_RECORD*    pLnk = (DBV_RECORD*)_pVectLink->At(ii);

      if (pLnk)
      {
         if (pLnk->_pszText)
         {
            delete[] pLnk->_pszText;
            pLnk->_pszText = NULL; 
         }

         if (pLnk->_pszComment)
         {
            delete[] pLnk->_pszComment;
            pLnk->_pszComment = NULL;
         }

         if (pLnk->_pArray)
         {
            delete[] pLnk->_pArray;
            pLnk->_pArray = NULL;
         }

         delete pLnk;
         pLnk = NULL;
      }
   }

   if (_pVectLink)
   {
      delete _pVectLink;
      _pVectLink = NULL;
   }
}

/* ******************************************************************** **
** @@ AppendFix2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void AppendFix2
(
   DBX_TABLE*           pTable,
   DWORD                dwIndexFrom,
   DWORD                dwLinkFrom
)
{
   BYTE     _Record[MAX_PATH];

   memset(&_Record,0x20,MAX_PATH);

   DBX_COLUMN*    pIndexFrom = pTable->GetColumn("INDEX FROM");
   DBX_COLUMN*    pLinkFrom  = pTable->GetColumn("LINK FROM");

   ASSERT(pIndexFrom);
   ASSERT(pLinkFrom);

   pIndexFrom->Set(&_Record,&dwIndexFrom);
   pLinkFrom-> Set(&_Record,&dwLinkFrom);

   pTable->InsertRecord((BYTE*)&_Record);
}

/* ******************************************************************** **
** @@ AppendFix3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void AppendFix3
(
   DBX_TABLE*        pTable,
   DWORD             dwRecNum,
   DWORD             dwIndexFrom,
   DWORD             dwLinkFrom,
   DWORD             dwLinkTo,
   DWORD             dwLinkCnt,
   DWORD             dwText,
   DWORD             dwCmnt,
   BYTE              byFlags
)
{
   BYTE     _Record[MAX_PATH];

   memset(&_Record,0x20,MAX_PATH);

   DBX_COLUMN*    pRecNum    = pTable->GetColumn("RECORD NUM");
   DBX_COLUMN*    pIndexFrom = pTable->GetColumn("INDEX FROM");
   DBX_COLUMN*    pLinkFrom  = pTable->GetColumn("LINK FROM");
   DBX_COLUMN*    pLinkTo    = pTable->GetColumn("LINK TO");
   DBX_COLUMN*    pLinkCnt   = pTable->GetColumn("LINK CNT");
   DBX_COLUMN*    pText      = pTable->GetColumn("TEXT");
   DBX_COLUMN*    pComment   = pTable->GetColumn("COMMENT");
   DBX_COLUMN*    pTimestamp = pTable->GetColumn("TIMESTAMP");
   DBX_COLUMN*    pBlock     = pTable->GetColumn("BLOCK");
   DBX_COLUMN*    pFlags     = pTable->GetColumn("FLAGS");

   ASSERT(pRecNum);
   ASSERT(pIndexFrom);
   ASSERT(pLinkFrom);
   ASSERT(pLinkTo);
   ASSERT(pLinkCnt);
   ASSERT(pText);
   ASSERT(pComment);
   ASSERT(pTimestamp);
   ASSERT(pBlock);
   ASSERT(pFlags);

   pRecNum->   Set(&_Record,&dwRecNum);
   pIndexFrom->Set(&_Record,&dwIndexFrom);
   pLinkFrom-> Set(&_Record,&dwLinkFrom);
   pLinkTo->   Set(&_Record,&dwLinkTo);
   pLinkCnt->  Set(&_Record,&dwLinkCnt);
   pText->     Set(&_Record,&dwText);
   pComment->  Set(&_Record,&dwCmnt);
   
   FILETIME    TimeNow;

   GetSystemTimeAsFileTime(&TimeNow);

   WORD        wFatDate = 0;
   WORD        wFatTime = 0;

   FileTimeToDosDateTime(&TimeNow,&wFatDate,&wFatTime);

   DWORD    dwTimestamp = (wFatDate << 16) | wFatTime;

   pTimestamp->Set(&_Record,&dwTimestamp);

   DWORD    dwBlock = dwLinkFrom / _dwPageSize3;

   pBlock->Set(&_Record,&dwBlock);

   DWORD    dwFlags = byFlags;

   pFlags->Set(&_Record,&dwFlags);

   pTable->InsertRecord((BYTE*)&_Record);
}

/* ******************************************************************** **
** @@ AppendVar3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static DWORD AppendVar3
(
   DBX_TABLE*           pTable,
//   DWORD                dwLinkFrom,
   const BYTE* const    pData,
   DWORD                dwSize
)
{
   if (!pData || !dwSize)
   {
      // Nothing to do !
      return 0;
   }

   ASSERT(pTable->_hVarFile != INVALID_HANDLE_VALUE);

   DWORD    dwFileSize = GetFileSize(pTable->_hVarFile,NULL);

   DWORD    dwBound = 0;

   if (_dwGranulation)
   {
      dwBound = ((dwFileSize + ((1 << _dwGranulation) - 1)) >> _dwGranulation) << _dwGranulation;
   }
   else
   {
      dwBound = dwFileSize;
   }

   DWORD    dwDelta = dwBound - dwFileSize;

   ASSERT(dwDelta < (WORD)(1 << _dwGranulation));

   if (dwDelta)
   {
      WriteBuffer(pTable->_hVarFile,_pDummy,dwDelta);
   }

//   dwSize += sizeof(DWORD);   // For dwLinkFrom !

   WriteBuffer(pTable->_hVarFile,&dwSize,sizeof(DWORD));
//   WriteBuffer(pTable->_hVarFile,&dwLinkFrom,sizeof(DWORD));
   WriteBuffer(pTable->_hVarFile,(void*)pData,dwSize);

   return dwBound;
}

/* ******************************************************************** **
** @@ AppendFix4()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void AppendFix4
(
   DBX_TABLE*           pTable,
   DWORD                dwLinkTo,
   DWORD                dwLinkFrom,
   DWORD                dwRecNum
)
{
   BYTE     _Record[MAX_PATH];

   memset(&_Record,0x20,MAX_PATH);

   DBX_COLUMN*    pLinkTo   = pTable->GetColumn("LINK TO");
   DBX_COLUMN*    pLinkFrom = pTable->GetColumn("LINK FROM");
//   DBX_COLUMN*    pRecNum   = pTable->GetColumn("RECORD NUN");

   ASSERT(pLinkTo);
   ASSERT(pLinkFrom);
//   ASSERT(pRecNum);

   pLinkTo->  Set(&_Record,&dwLinkTo);
   pLinkFrom->Set(&_Record,&dwLinkFrom);
//   pRecNum->  Set(&_Record,&RecNum);

   pTable->InsertRecord((BYTE*)&_Record);
}

/* ******************************************************************** **
** @@ Append2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Append2
(
   DBX_TABLE*           pTable,
   DWORD                dwIndexFrom,
   DWORD                dwLinkFrom
)
{
   ASSERT(pTable);
   ASSERT(dwLinkFrom);

   AppendFix2(pTable,dwIndexFrom,dwLinkFrom);
}

/* ******************************************************************** **
** @@ Append3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Append3
(
   DBX_TABLE*           pTable,
   DWORD                dwRecNum,
   DWORD                dwIndexFrom,
   DWORD                dwLinkFrom,
   DWORD                dwLinkTo,
   DWORD                dwLinkCnt,
   const char* const    pszText,
   DWORD                dwTextSize,
   const char* const    pszComment,
   DWORD                dwCommentSize,
   BYTE                 byFlags
)
{
   ASSERT(pTable);
   ASSERT(dwRecNum);
   ASSERT(dwLinkFrom);
   ASSERT(dwLinkTo);
   ASSERT(dwTextSize);

   DWORD    dwText = AppendVar3(pTable/*,dwLinkFrom*/,(BYTE*)pszText,   dwTextSize);
   DWORD    dwCmnt = AppendVar3(pTable/*,dwLinkFrom*/,(BYTE*)pszComment,dwCommentSize);

   AppendFix3(pTable,dwRecNum,dwIndexFrom,dwLinkFrom,dwLinkTo,dwLinkCnt,dwText,dwCmnt,byFlags);
}

/* ******************************************************************** **
** @@ Append4()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Append4
(
   DBX_TABLE*           pTable,
   DWORD                dwLinkTo,
   DWORD                dwLinkFrom,
   DWORD                dwRecNum
)
{
   ASSERT(pTable);
   ASSERT(dwLinkTo);
   ASSERT(dwLinkFrom);
   ASSERT(dwRecNum);

   AppendFix4(pTable,dwLinkTo,dwLinkFrom,dwRecNum);
}

/* ******************************************************************** **
** @@ Updater2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Updater2()
{
   DBX*     pDBX = new DBX;

   DBX_TABLE*     pDst2 = pDBX->OpenTable
   (
      (LPCTSTR)_sTable10_RU_NEW,
      (LPCTSTR)_sTable10_RU_NEW_DBF,
      NULL,
      DBX_OM_READ_WRITE,
      DBX_OM_NONE,
      DBX_FM_FLUSH_ON_CLOSE,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pDst2)
   {
      // Error !
      ASSERT(0);
      return;
   }

   DWORD    dwRecCnt = _pVectSrc->Count();

   ASSERT(dwRecCnt);

   for (DWORD ii = 0; ii < dwRecCnt; ++ii)
   {
      DBV_RECORD*       pRec = (DBV_RECORD*)_pVectSrc->At(ii);

      ASSERT(pRec);

      if (pRec)
      {
         DWORD    dwIndexFrom = pRec->_dwIndexFrom;
         DWORD    dwLinkFrom  = pRec->_dwLink;

         Append2(pDst2,dwIndexFrom,dwLinkFrom);
      }
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Updater3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Updater3()
{
   DBX*     pDBX = new DBX;

   DBX_TABLE*     pDst3 = pDBX->OpenTable
   (
      (LPCTSTR)_sTable10_RU_LINK,
      (LPCTSTR)_sTable10_RU_LINK_DBF,
      (LPCTSTR)_sTable10_RU_LINK_DBV,
      DBX_OM_READ_WRITE,
      DBX_OM_READ_WRITE,
      DBX_FM_FLUSH_ON_CLOSE,
      DBX_FM_FLUSH_ON_CLOSE
   );
   
   if (!pDst3)
   {
      // Error !
      ASSERT(0);
      return;
   }

   DBX_TABLE*     pDst4 = pDBX->OpenTable
   (
      (LPCTSTR)_sTable10_RU_MAP,
      (LPCTSTR)_sTable10_RU_MAP_DBF,
      NULL,
      DBX_OM_READ_WRITE,
      DBX_OM_NONE,
      DBX_FM_FLUSH_ON_CLOSE,
      DBX_FM_FLUSH_NEVER
   );
   
   if (!pDst4)
   {
      // Error !
      ASSERT(0);
      delete pDBX;
      pDBX = NULL;
      return;
   }

   DWORD    dwRecCnt = _pVectLink->Count();

   ASSERT(dwRecCnt);

   _dwPageSize3 = (dwRecCnt + 255) / 256; // 256 blocks max !

   for (DWORD ii = 0; ii < dwRecCnt; ++ii)
   {
      DBV_RECORD*       pRec = (DBV_RECORD*)_pVectLink->At(ii);

      ASSERT(pRec);

      if (pRec)
      {
         DWORD    dwRecNum    = pRec->_dwRecNum;
         DWORD    dwIndexFrom = pRec->_dwIndexFrom;
         DWORD    dwLinkCnt   = pRec->_iLinkCnt;

         char*    pszText    = pRec->_pszText;
         DWORD    dwTextSize = pRec->_dwTextSize;

         char*    pszComment    = pRec->_pszComment;
         DWORD    dwCommentSize = pRec->_dwCommentSize;
        
         BYTE     byFlags = (BYTE)pRec->_wFlags;

         Append3(pDst3,dwRecNum,dwIndexFrom,ii + 1,ii + 1,dwLinkCnt,pszText,dwTextSize,pszComment,dwCommentSize,byFlags);
         Append4(pDst4,ii + 1,ii + 1,ii + 1);
      }
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Creator2()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Creator2(const DBX_TABLE_INFO& rInfo)
{
   DBX*     pDBX = new DBX;

   if (!pDBX->CreateEmptyTable(&rInfo))
   {
      // Error !
      ASSERT(0);
      return;
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Creator3()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Creator3(const DBX_TABLE_INFO& rInfo)
{
   DBX*     pDBX = new DBX;

   if (!pDBX->CreateEmptyTable(&rInfo))
   {
      // Error !
      ASSERT(0);
      return;
   }

   if (!pDBX->CreateEmptyMemo((LPCTSTR)_sTable10_RU_LINK_DBV,_dwGranulation))
   {
      // Error !
      ASSERT(0);
      return;
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ Creator4()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void Creator4(const DBX_TABLE_INFO& rInfo)
{
   DBX*     pDBX = new DBX;

   if (!pDBX->CreateEmptyTable(&rInfo))
   {
      // Error !
      ASSERT(0);
      return;
   }

   delete pDBX;
   pDBX = NULL;
}

/* ******************************************************************** **
** @@ ForEach()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void ForEach(const char* const pszFilename)
{
   char     pszDrive   [_MAX_DRIVE];
   char     pszDir     [_MAX_DIR];
   char     pszFName   [_MAX_FNAME];
   char     pszExt     [_MAX_EXT];

   _splitpath(pszFilename,pszDrive,pszDir,pszFName,pszExt);

   switch (*pszFName)
   {
      case 'm':
      case 'M':
      {
         _sTable10_RU          = "M_Russian_10";
         _sTable10_RU_DBF      = "M_Russian_10.dbf";
         _sTable10_RU_DBV      = "M_Russian_10.dbv";
         _sTable10_RU_NEW      = "M_Russian_10_";
         _sTable10_RU_NEW_DBF  = "M_Russian_10_.dbf";
//         _sTable10_RU_NEW_DBV = "M_Russian_10_.dbv";
         _sTable10_RU_LINK    = "M_Link_10";
         _sTable10_RU_LINK_DBF = "M_Link_10.dbf";
         _sTable10_RU_LINK_DBV = "M_Link_10.dbv";
         _sTable10_RU_MAP      = "M_Mapper_10";
         _sTable10_RU_MAP_DBF  = "M_Mapper_10.dbf";
         break;
      }
      case 'u':
      case 'U':
      {
         _sTable10_RU          = "U_Russian_10";
         _sTable10_RU_DBF      = "U_Russian_10.dbf";
         _sTable10_RU_DBV      = "U_Russian_10.dbv";
         _sTable10_RU_NEW      = "U_Russian_10_";
         _sTable10_RU_NEW_DBF  = "U_Russian_10_.dbf";
//         _sTable10_RU_NEW_DBV = "U_Russian_10_.dbv";
         _sTable10_RU_LINK    = "U_Link_10";
         _sTable10_RU_LINK_DBF = "U_Link_10.dbf";
         _sTable10_RU_LINK_DBV = "U_Link_10.dbv";
         _sTable10_RU_MAP      = "U_Mapper_10";
         _sTable10_RU_MAP_DBF  = "U_Mapper_10.dbf";
         break;
      }
      case 'v':
      case 'V':
      {
         _sTable10_RU          = "V_Russian_10";
         _sTable10_RU_DBF      = "V_Russian_10.dbf";
         _sTable10_RU_DBV      = "V_Russian_10.dbv";
         _sTable10_RU_NEW      = "V_Russian_10_";
         _sTable10_RU_NEW_DBF  = "V_Russian_10_.dbf";
//         _sTable10_RU_NEW_DBV = "V_Russian_10_.dbv";
         _sTable10_RU_LINK     = "V_Link_10";
         _sTable10_RU_LINK_DBF = "V_Link_10.dbf";
         _sTable10_RU_LINK_DBV = "V_Link_10.dbv";
         _sTable10_RU_MAP      = "V_Mapper_10";
         _sTable10_RU_MAP_DBF  = "V_Mapper_10.dbf";
         break;
      }
      default:
      {
         // Error !
         ASSERT(0);
         return;
      }
   }

   const int      FIELD_CNT = 5;

   DBX_COLUMN_DESCRIPTOR    pFieldArr[FIELD_CNT];

   memset(pFieldArr,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT);

   // 1. IDX FROM
   DefineField(pFieldArr, 0,"INDEX FROM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. TEXT
   DefineField(pFieldArr, 1,"TEXT",      DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. COMMENT
   DefineField(pFieldArr, 2,"COMMENT",   DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 4. ARRAY
   DefineField(pFieldArr, 3,"ARRAY",     DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 5. FLAGS
   DefineField(pFieldArr, 4,"FLAGS",     DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(BYTE));

   _InfoSrc._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoSrc._iCnt      = FIELD_CNT;
   _InfoSrc._pFieldArr = pFieldArr;

   strcpy((char*)&_InfoSrc._pszName,(LPCTSTR)_sTable10_RU_DBF);

   Load();

   Reduce();

   CopySingles(); // The rest !

   const int      FIELD_CNT2 = 2;

   DBX_COLUMN_DESCRIPTOR    pFieldArr2[FIELD_CNT];

   memset(pFieldArr2,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT2);

   // 1. INDEX FROM
   DefineField(pFieldArr2, 0,"INDEX FROM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. LINK FROM
   DefineField(pFieldArr2, 1,"LINK FROM", DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));

   _InfoNew._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoNew._iCnt      = FIELD_CNT2;
   _InfoNew._pFieldArr = pFieldArr2;

   strcpy((char*)&_InfoNew._pszName,(LPCTSTR)_sTable10_RU_NEW_DBF);

   Creator2(_InfoNew);
   Updater2();

   const int      FIELD_CNT3 = 10;

   DBX_COLUMN_DESCRIPTOR    pFieldArr3[FIELD_CNT];

   memset(pFieldArr3,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT3);

   // 1. RECORD NUM
   DefineField(pFieldArr3, 0,"RECORD NUM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. INDEX FROM
   DefineField(pFieldArr3, 1,"INDEX FROM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. LINK FROM
   DefineField(pFieldArr3, 2,"LINK FROM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 4. LINK TO
   DefineField(pFieldArr3, 3,"LINK TO",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 5. LINK CNT
   DefineField(pFieldArr3, 4,"LINK CNT", DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 6. TEXT
   DefineField(pFieldArr3, 5,"TEXT",     DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 7. COMMENT
   DefineField(pFieldArr3, 6,"COMMENT",  DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 8. TIMESTAMP
   DefineField(pFieldArr3, 7,"TIMESTAMP",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 9. BLOCK
   DefineField(pFieldArr3, 8,"BLOCK",    DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(BYTE));
   // 10. FLAGS
   DefineField(pFieldArr3, 9,"FLAGS",    DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(BYTE));

   _InfoLink._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoLink._iCnt      = FIELD_CNT3;
   _InfoLink._pFieldArr = pFieldArr3;

   strcpy((char*)&_InfoLink._pszName,(LPCTSTR)_sTable10_RU_LINK_DBF);

   Creator3(_InfoLink);

   const int      FIELD_CNT4 = 3;

   DBX_COLUMN_DESCRIPTOR    pFieldArr4[FIELD_CNT4];

   memset(pFieldArr4,0,sizeof(DBX_COLUMN_DESCRIPTOR) * FIELD_CNT4);

   // 1. LINK TO
   DefineField(pFieldArr4, 0,"LINK TO",   DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 2. LINK FROM
   DefineField(pFieldArr4, 1,"LINK FROM", DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));
   // 3. RECORD NUM
   DefineField(pFieldArr4, 2,"RECORD NUM",DBX_FLT_CHARACTER,DBX_FF_BINARY,sizeof(DWORD));

   _InfoMap._FileType  = DBX_FT_FOX_BASE_PLUS_NO_MEMO;
   _InfoMap._iCnt      = FIELD_CNT4;
   _InfoMap._pFieldArr = pFieldArr4;

   strcpy((char*)&_InfoMap._pszName,(LPCTSTR)_sTable10_RU_MAP_DBF);

   Creator4(_InfoMap);

   Updater3();

   Cleanup();
}

/* ******************************************************************** **
** @@ ShowHelp()
** @  Copyrt :
** @  Author :
** @  Modify :
** @  Update :
** @  Notes  :
** ******************************************************************** */

static void ShowHelp()
{
   const char  pszCopyright[] = "-*-   DBX Remapper  1.0   *   Copyright (c) Gazlan, 2015   -*-";
   const char  pszDescript [] = "DBX Remapper";
   const char  pszE_Mail   [] = "complains_n_suggestions direct to gazlan@yandex.ru";

   printf("%s\n\n",pszCopyright);
   printf("%s\n\n",pszDescript);
   printf("Usage: dbx_remapper.com wildcards\n\n");
   printf("%s\n",pszE_Mail);
}

/* ******************************************************************** **
** @@ main()
** @ Copyrt:
** @ Author:
** @ Modify:
** @ Update:
** @ Notes :
** ******************************************************************** */

int main(int argc,char** argv)
{
   if (argc != 2)
   {
      ShowHelp();
      return 0;
   }

   if (argc == 2 && ((!strcmp(argv[1],"?")) || (!strcmp(argv[1],"/?")) || (!strcmp(argv[1],"-?")) || (!stricmp(argv[1],"/h")) || (!stricmp(argv[1],"-h"))))
   {
      ShowHelp();
      return 0;
   }

   char     pszMask[MAX_PATH + 1];
   
   memset(pszMask,0,sizeof(pszMask));
   
   strncpy(pszMask,argv[1],MAX_PATH);
   pszMask[MAX_PATH] = 0; // Ensure ASCIIZ
   
   char     pszDrive[_MAX_DRIVE];
   char     pszDir  [_MAX_DIR];
   char     pszFName[_MAX_FNAME];
   char     pszExt  [_MAX_EXT];
   
   _splitpath(pszMask,pszDrive,pszDir,pszFName,pszExt);
   
   char     pszSrchMask[MAX_PATH + 1];
   char     pszSrchPath[MAX_PATH + 1];
   
   strcpy(pszSrchMask,pszFName);
   strcat(pszSrchMask,pszExt);
   
   Walker      Visitor;

   Visitor.Init(ForEach,pszSrchMask,false);

   strcpy(pszSrchPath,pszDrive);
   strcat(pszSrchPath,pszDir);

   Visitor.Run(*pszSrchPath  ?  pszSrchPath  :  ".");

   return 0;
}

/* ******************************************************************** **
**                That's All
** ******************************************************************** */
