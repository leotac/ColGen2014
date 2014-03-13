/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */
/*                                                                           */
/*                  This file is part of the program and library             */
/*         SCIP --- Solving Constraint Integer Programs                      */
/*                                                                           */
/*    Copyright (C) 2002-2014 Konrad-Zuse-Zentrum                            */
/*                            fuer Informationstechnik Berlin                */
/*                                                                           */
/*  SCIP is distributed under the terms of the ZIB Academic License.         */
/*                                                                           */
/*  You should have received a copy of the ZIB Academic License              */
/*  along with SCIP; see the file COPYING. If not email to scip@zib.de.      */
/*                                                                           */
/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

/**@file   reader_bpa.c
 * @brief  Binpacking problem reader file reader
 * @author Timo Berthold
 * @author Stefan Heinz
 */

/*---+----1----+----2----+----3----+----4----+----5----+----6----+----7----+----8----+----9----+----0----+----1----+----2*/

#include <assert.h>
#include <string.h>

#include "scip/cons_setppc.h"

#include "pricer_binpacking.h"
#include "reader_bpa.h"

/**@name Reader properties
 *
 * @{
 */

#define READER_NAME             "bpareader"
#define READER_DESC             "file reader for binpacking data format"
#define READER_EXTENSION        "bpa"

/**@} */


/**@name Callback methods
 *
 * @{
 */

/** problem reading method of reader */
static
SCIP_DECL_READERREAD(readerReadBpa)
{  /*lint --e{715}*/
   SCIP_FILE* file;
   SCIP_CONS** conss;
   SCIP_Longint* weights;
   SCIP_Bool error;

   char name[SCIP_MAXSTRLEN];
   char format[16];
   char buffer[SCIP_MAXSTRLEN];
   int capacity;
   int nitems;
   int bestsolvalue;
   int nread;
   int weight;
   int nweights;
   int lineno;
   int i;

   *result = SCIP_DIDNOTRUN;

   /* open file */
   file = SCIPfopen(filename, "r");
   if( file == NULL )
   {
      SCIPerrorMessage("cannot open file <%s> for reading\n", filename);
      SCIPprintSysError(filename);
      return SCIP_NOFILE;
   }

   lineno = 0;

   /* read problem name */
   if( !SCIPfeof(file) )
   {
      /* get next line */
      if( SCIPfgets(buffer, sizeof(buffer), file) == NULL )
         return SCIP_READERROR;
      lineno++;

      /* parse dimension line */
      sprintf(format, "%%%ds\n", SCIP_MAXSTRLEN);
      nread = sscanf(buffer, format, name);
      if( nread == 0 )
      {
         SCIPwarningMessage(scip, "invalid input line %d in file <%s>: <%s>\n", lineno, filename, buffer);
         return SCIP_READERROR;
      }

      SCIPdebugMessage("problem name <%s>\n", name);
   }

   /* read problem dimension */
   if( !SCIPfeof(file) )
   {
      /* get next line */
      if( SCIPfgets(buffer, sizeof(buffer), file) == NULL )
         return SCIP_READERROR;
      lineno++;

      /* parse dimension line */
      nread = sscanf(buffer, "%d %d %d\n", &capacity, &nitems, &bestsolvalue);
      if( nread < 2 )
      {
         SCIPwarningMessage(scip, "invalid input line %d in file <%s>: <%s>\n", lineno, filename, buffer);
         return SCIP_READERROR;
      }

      SCIPdebugMessage("capacity = <%d>, number of items = <%d>, best known solution = <%d>\n", capacity, nitems, bestsolvalue);
   }


   /* allocate buffer memory for storing the weights temporarily */
   SCIP_CALL( SCIPallocBufferArray(scip, &weights, nitems) );

   /* parse weights */
   nweights = 0;
   error = FALSE;

   while( !SCIPfeof(file) && !error )
   {
      /* get next line */
      if( SCIPfgets(buffer, sizeof(buffer), file) == NULL )
         break;
      lineno++;

      /* parse the line */
      nread = sscanf(buffer, "%d\n", &weight);
      if( nread == 0 )
      {
         SCIPwarningMessage(scip, "invalid input line %d in file <%s>: <%s>\n", lineno, filename, buffer);
         error = TRUE;
         break;
      }

      SCIPdebugMessage("found weight %d <%d>\n", nweights, weight);
      weights[nweights] = weight;
      nweights++;

      if( nweights == nitems )
         break;
   }

   if( nweights < nitems )
   {
      SCIPwarningMessage(scip, "set nitems from <%d> to <%d> since the file <%s> only contains <%d> weights\n", nitems, weights, filename, weights);
      nitems = nweights;
   }

   if( error )
      goto TERMINATE;
   
   /* create a new problem in SCIP */  
   SCIP_CALL( SCIPcreateProbBasic(scip, name) );

   SCIP_CALL( SCIPallocBufferArray(scip, &conss, nitems) );
   
   /* create start solution each item in exactly one bin */
   for( i = 0; i < nitems; ++i )
   {
      SCIP_VAR* var;

      sprintf(name, "item_%d", i);

      /* create variable for the packing pattern which contains only this item */
      SCIP_CALL( SCIPcreateVarBasic(scip, &var, name, 0.0, 1.0, 1.0, SCIP_VARTYPE_BINARY) );
      SCIP_CALL( SCIPvarSetRemovable(var, TRUE) );
      SCIP_CALL( SCIPaddVar(scip, var) );
      
      SCIP_CALL( SCIPcreateConsSetcover(scip, &conss[i], name, 
            1, &var, TRUE, TRUE, TRUE, TRUE, TRUE, FALSE, TRUE, FALSE, FALSE, FALSE) );
      SCIP_CALL( SCIPaddCons(scip, conss[i]) );   

      /* release variable */
      SCIP_CALL( SCIPreleaseVar(scip, &var) );
   }   
   
   SCIP_CALL( SCIPpricerBinpackingActivate(scip, conss, weights, nweights, capacity) );
   
   SCIP_CALL( SCIPsetObjIntegral(scip) );

   for( i = 0; i < nitems; ++i )
   {
      SCIP_CALL( SCIPreleaseCons(scip, &conss[i]) );
   }

 TERMINATE:
   (void) SCIPfclose(file);
   SCIPfreeBufferArray(scip, &weights);

   if( error )
      return SCIP_READERROR;

   *result = SCIP_SUCCESS;

   return SCIP_OKAY;
}

/**@} */


/**@name Interface methods
 *
 * @{
 */

/** includes the bpa file reader in SCIP */
SCIP_RETCODE SCIPincludeReaderBpa(
   SCIP*                 scip                /**< SCIP data structure */
   )
{
   SCIP_READERDATA* readerdata;
   SCIP_READER* reader;

   /* create binpacking reader data */
   readerdata = NULL;

   /* include binpacking reader */
   SCIP_CALL( SCIPincludeReaderBasic(scip, &reader, READER_NAME, READER_DESC, READER_EXTENSION, readerdata) );
   assert(reader != NULL);

   SCIP_CALL( SCIPsetReaderRead(scip, reader, readerReadBpa) );

   return SCIP_OKAY;
}

/**@} */
