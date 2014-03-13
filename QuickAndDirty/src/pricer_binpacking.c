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

/**@file   pricer_binpacking.c
 * @brief  Binpacking variable pricer
 * @author Timo Berthold
 * @author Stefan Heinz
 */

/*---+----1----+----2----+----3----+----4----+----5----+----6----+----7----+----8----+----9----+----0----+----1----+----2*/

#include <assert.h>
#include <string.h>

#include "scip/cons_knapsack.h"
#include "scip/cons_setppc.h"
#include "scip/scipdefplugins.h"

#include "pricer_binpacking.h"

/**@name Pricer properties
 *
 * @{
 */

#define PRICER_NAME            "binpacking"
#define PRICER_DESC            "pricer for binpacking tours"
#define PRICER_PRIORITY        0
#define PRICER_DELAY           TRUE     /* only call pricer if all problem variables have non-negative reduced costs */

/**@} */


/*
 * Data structures
 */

/** @brief Variable pricer data used in the \ref pricer_binpacking.c "pricer" */
struct SCIP_PricerData
{
   SCIP_CONS**           conss;              /**< set covering constraints for the items */
   SCIP_Longint*         weights;            /**< weight of the items */
   int                   nitems;             /**< number of items to be packed */
   SCIP_Longint          capacity;           /**< capacity of the bins */
};



/**@} */

/**name Callback methods
 *
 * @{
 */

/** destructor of variable pricer to free user data (called when SCIP is exiting) */
static
SCIP_DECL_PRICERFREE(pricerFreeBinpacking)
{
   SCIP_PRICERDATA* pricerdata;

   assert(scip != NULL);
   assert(pricer != NULL);

   pricerdata = SCIPpricerGetData(pricer);

   if( pricerdata != NULL)
   {
      /* free memory */
      SCIPfreeMemoryArrayNull(scip, &pricerdata->conss);
      SCIPfreeMemoryArrayNull(scip, &pricerdata->weights);

      SCIPfreeMemory(scip, &pricerdata);
   }

   return SCIP_OKAY;
}


/** initialization method of variable pricer (called after problem was transformed) */
static
SCIP_DECL_PRICERINIT(pricerInitBinpacking)
{  /*lint --e{715}*/
   SCIP_PRICERDATA* pricerdata;
   SCIP_VAR** vars;
   SCIP_CONS* cons;
   int nvars;
   int c;

   assert(scip != NULL);
   assert(pricer != NULL);

   pricerdata = SCIPpricerGetData(pricer);
   assert(pricerdata != NULL);

   /* get transformed constraints */
   for( c = 0; c < pricerdata->nitems; ++c )
   {
      cons = pricerdata->conss[c];

      /* release original constraint */
      SCIP_CALL( SCIPreleaseCons(scip, &pricerdata->conss[c]) );

      /* get transformed constraint */
      SCIP_CALL( SCIPgetTransformedCons(scip, cons, &pricerdata->conss[c]) );

      /* capture transformed constraint */
      SCIP_CALL( SCIPcaptureCons(scip, pricerdata->conss[c]) );
   }

   /* set the upper bound for each decision variable to lazy since these upper bounds are enforced through the set
    * packing constraints */
   vars = SCIPgetVars(scip);
   nvars = SCIPgetNVars(scip);
   for( c = 0; c < nvars; ++c )
   {
      SCIP_CALL( SCIPchgVarUbLazy(scip, vars[c], 1.0) );
   }

   return SCIP_OKAY;
}


/** solving process deinitialization method of variable pricer (called before branch and bound process data is freed) */
static
SCIP_DECL_PRICEREXITSOL(pricerExitsolBinpacking)
{
   SCIP_PRICERDATA* pricerdata;
   int c;

   assert(scip != NULL);
   assert(pricer != NULL);

   pricerdata = SCIPpricerGetData(pricer);
   assert(pricerdata != NULL);

   /* get release constraints */
   for( c = 0; c < pricerdata->nitems; ++c )
   {
      /* release constraint */
      SCIP_CALL( SCIPreleaseCons(scip, &(pricerdata->conss[c])) );
   }

   return SCIP_OKAY;
}


/** reduced cost pricing method of variable pricer for feasible LPs */
static
SCIP_DECL_PRICERREDCOST(pricerRedcostBinpacking)
{  /*lint --e{715}*/
   SCIP_PRICERDATA* pricerdata;
   SCIP_CONS** conss;
   SCIP_Longint* weights;
   SCIP_Real* profits;
   int* solitems;
   int* nonsolitems;
   int* items;

   int nitems;
   int nsolitems;
   int nnonsolitems;
   SCIP_Real solval;
   SCIP_Longint capacity;
   SCIP_Bool success;
   int i;

   assert(scip != NULL);
   assert(pricer != NULL);

   (*result) = SCIP_DIDNOTRUN;

   /* get the pricer data */
   pricerdata = SCIPpricerGetData(pricer);
   assert(pricerdata != NULL);

   capacity = pricerdata->capacity;
   conss = pricerdata->conss;
   nitems = pricerdata->nitems;

   /* allocate memory for profit array, solution array, non solution array, and items array */
   SCIP_CALL( SCIPallocBufferArray(scip, &items, nitems) );
   SCIP_CALL( SCIPallocBufferArray(scip, &profits, nitems) );
   SCIP_CALL( SCIPallocBufferArray(scip, &solitems, nitems) );
   SCIP_CALL( SCIPallocBufferArray(scip, &nonsolitems, nitems) );

   /* copy the weights array */
   SCIP_CALL( SCIPduplicateBufferArray(scip, &weights, pricerdata->weights, nitems) );
   
   nsolitems = 0;
   nnonsolitems = 0;

   /* fill profit array with dual solution values */
   for( i = 0; i < nitems; i++ ) 
   {
      /* TODO: fill the profit array with the dual values */

      items[i] = i;
   }
   
#ifdef SCIP_DEBUG
   /* debug output; this one turned on using "#define SCIP_DEBUG" */

   SCIPdebugMessage("   nitems: %d capacity: %"SCIP_LONGINT_FORMAT"\n", nitems, capacity);
   SCIPdebugMessage(" %4s %4s %7s\n", "#", "dual", "weights");
   for( i = 0; i < nitems; ++i ) 
   {
      SCIPdebugMessage("%4.2f %7"SCIP_LONGINT_FORMAT"\n", profits[i], weights[i]);
   }
#endif
   
   /* TODO: solve the knapsack problem */

   
#ifdef SCIP_DEBUG
   /* debug output; this one is turned by using "#define SCIP_DEBUG" */

   SCIPdebugMessage("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX\n");
   SCIPdebugMessage("X Knapsack algorithm calculated reduced costs of %f X \n", redcost);
   SCIPdebugMessage("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX\n");   

   {
      int item;
      SCIP_Longint usedcapacity;

      usedcapacity = 0;
      
      SCIPdebugMessage(" nitems: %d capacity: %"SCIP_LONGINT_FORMAT"\n", nitems, capacity);
      SCIPdebugMessage(" %4s %7s\n", "#", "weights");
      for( i = 0; i < nsolitems; ++i ) 
      {
         item  = solitems[i];
         usedcapacity += weights[item];
         SCIPdebugMessage(" %4d %7"SCIP_LONGINT_FORMAT"\n", item, pricerdata->weights[item]);
      }
      assert(usedcapacity <= capacity);
   }
#endif
   
   /* TODO: replace FALSE with the check if we found a solution with negative reduced cost */
   if( FALSE ) 
   {
      SCIP_VAR* var;
         
      /* TODO: create a suitable variable name; this might help for debugging */
      
         
      /* TODO: create a new binary variable */
            

      /* TODO: add the new variable to the pricer store */

         
      /* change the upper bound of the binary variable to lazy since the upper bound is already enforced 
       * due to the objective function the set covering constraint;
       * The reason for doing is to avoid the bound of x <= 1 in the LP relaxation since this bound
       * constraint would produce a dual variable which might have a positive reduced cost 
       */
      SCIP_CALL( SCIPchgVarUbLazy(scip, var, 1.0) );
      
      /* TODO: add the new variable to the corresponding set covering constraints */
      
      /* TODO: release the new variable such that SCIP takes care of it */
   }

   (*result) = SCIP_SUCCESS;
   
   /* free buffer arrays */
   SCIPfreeBufferArray(scip, &weights);
   SCIPfreeBufferArray(scip, &nonsolitems);
   SCIPfreeBufferArray(scip, &solitems);
   SCIPfreeBufferArray(scip, &profits);
   SCIPfreeBufferArray(scip, &items);

   return SCIP_OKAY;
}


/** farkas pricing method of variable pricer for infeasible LPs */
static
SCIP_DECL_PRICERFARKAS(pricerFarkasBinpacking)
{  /*lint --e{715}*/

   /** @note In case of this binpacking example, the master LP should not get infeasible after branching, because of the
    *        way branching is performed. Therefore, the Farkas pricing is not implemented.
    *        1. In case of Ryan/Foster branching, the two items are selected in a way such that the sum of the LP values
    *           of all columns/packings containing both items is fractional. Hence, it exists at least one
    *           column/packing which contains both items and also at least one column/packing for each item containing
    *           this but not the other item. That means, branching in the "same" direction stays LP feasible since there
    *           exists at least one column/packing with both items and branching in the "differ" direction stays LP
    *           feasible since there exists at least one column/packing containing one item, but not the other.
    *        2. In case of variable branching, we only branch on fractional variables. If a variable is fixed to one,
    *           there is no issue.  If a variable is fixed to zero, then we know that for each item which is part of
    *           that column/packing, there exists at least one other column/packing containing this particular item due
    *           to the covering constraints.
    */
   SCIPwarningMessage(scip, "Current master LP is infeasible, but Farkas pricing was not implemented\n");
   SCIPABORT();

   return SCIP_OKAY;
}

/**@} */


/**@name Interface methods
 *
 * @{
 */

/** creates the binpacking variable pricer and includes it in SCIP */
SCIP_RETCODE SCIPincludePricerBinpacking(
   SCIP*                 scip                /**< SCIP data structure */
   )
{
   SCIP_PRICERDATA* pricerdata;
   SCIP_PRICER* pricer;

   /* create binpacking variable pricer data */
   SCIP_CALL( SCIPallocMemory(scip, &pricerdata) );

   pricerdata->conss = NULL;
   pricerdata->weights = NULL;
   pricerdata->nitems = 0;
   pricerdata->capacity = 0;

   /* include variable pricer */
   SCIP_CALL( SCIPincludePricerBasic(scip, &pricer, PRICER_NAME, PRICER_DESC, PRICER_PRIORITY, PRICER_DELAY,
         pricerRedcostBinpacking, pricerFarkasBinpacking, pricerdata) );

   SCIP_CALL( SCIPsetPricerFree(scip, pricer, pricerFreeBinpacking) );
   SCIP_CALL( SCIPsetPricerInit(scip, pricer, pricerInitBinpacking) );
   SCIP_CALL( SCIPsetPricerExitsol(scip, pricer, pricerExitsolBinpacking) );

   /* add binpacking variable pricer parameters */

   return SCIP_OKAY;
}


/** added problem specific data to pricer and activates pricer */
SCIP_RETCODE SCIPpricerBinpackingActivate(
   SCIP*                 scip,               /**< SCIP data structure */
   SCIP_CONS**           conss,              /**< set covering constraints for the items */
   SCIP_Longint*         weights,            /**< weight of the items */
   int                   nitems,             /**< number of items to be packed */
   SCIP_Longint          capacity            /**< capacity of the bins */
   )
{
   SCIP_PRICER* pricer;
   SCIP_PRICERDATA* pricerdata;
   int c;

   assert(scip != NULL);
   assert(conss != NULL);
   assert(weights != NULL);
   assert(nitems > 0);

   pricer = SCIPfindPricer(scip, PRICER_NAME);
   assert(pricer != NULL);

   pricerdata = SCIPpricerGetData(pricer);
   assert(pricerdata != NULL);

   /* copy arrays */
   SCIP_CALL( SCIPduplicateMemoryArray(scip, &pricerdata->conss, conss, nitems) );
   SCIP_CALL( SCIPduplicateMemoryArray(scip, &pricerdata->weights, weights, nitems) );

   pricerdata->nitems = nitems;
   pricerdata->capacity = capacity;

   SCIPdebugMessage("   nitems: %d capacity: %"SCIP_LONGINT_FORMAT"  \n", nitems, capacity);
   SCIPdebugMessage("      # profits    weights   x  \n");   /* capture constraints */

   /* capture all constraints */
   for( c = 0; c < nitems; ++c )
   {
      SCIP_CALL( SCIPcaptureCons(scip, conss[c]) );
      SCIPdebugPrintf("%4d %3"SCIP_LONGINT_FORMAT"\n", c, weights[c]);
   }

   /* activate pricer */
   SCIP_CALL( SCIPactivatePricer(scip, pricer) );

   return SCIP_OKAY;
}

/**@} */
