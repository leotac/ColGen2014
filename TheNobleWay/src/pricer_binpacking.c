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
#include "scip/cons_logicor.h"
#include "scip/cons_setppc.h"
#include "scip/cons_varbound.h"
#include "scip/scipdefplugins.h"

#include "cons_samediff.h"
#include "pricer_binpacking.h"
#include "probdata_binpacking.h"
#include "vardata_binpacking.h"

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
   SCIP_CONSHDLR*        conshdlr;           /**< constraint handler for "same" and "diff" constraints */
   SCIP_CONS**           conss;              /**< set covering constraints for the items */
   SCIP_Longint*         weights;            /**< weight of the items */
   int*                  ids;                /**< array of item ids */
   int                   nitems;             /**< number of items to be packed */
   SCIP_Longint          capacity;           /**< capacity of the bins */
};



/**@name Local methods
 *
 * @{
 */

/** add branching decisions constraints to the subSCIP */
static
SCIP_RETCODE addBranchingDecisionConss(
   SCIP*                 scip,               /**< SCIP data structure */
   SCIP*                 subscip,            /**< pricing SCIP data structure */
   SCIP_VAR**            vars,               /**< variable array of the subscip variables */
   SCIP_CONSHDLR*        conshdlr            /**< constraint handler for branching data */
   )
{
   SCIP_CONS** conss;
   SCIP_CONS* cons;
   int nconss;
   int id1;
   int id2;
   CONSTYPE type;

   SCIP_Real vbdcoef;
   SCIP_Real lhs;
   SCIP_Real rhs;

   int c;

   SCIP_CONS* vbcons;
   
   assert(scip != NULL);
   assert(subscip != NULL);
   assert(conshdlr != NULL);

   /* collect all branching decision constraints */
   conss = SCIPconshdlrGetConss(conshdlr);
   nconss = SCIPconshdlrGetNConss(conshdlr);

   /* loop over all branching decision constraints and apply the branching decision if the corresponding constraint is
    * active
    */
   for( c = 0; c < nconss; ++c )
   {
      cons = conss[c];

      /* ignore constraints which are not active since these are not laying on the current active path of the search
       * tree
       */
      if( !SCIPconsIsActive(cons) )
         continue;

      /* collect the two item ids and the branching type (SAME or DIFFER) on which the constraint branched */
      id1 = SCIPgetItemid1Samediff(scip, cons);
      id2 = SCIPgetItemid2Samediff(scip, cons);
      type = SCIPgetTypeSamediff(scip, cons);

      SCIPdebugMessage("create varbound for %s(%d,%d)\n", type == SAME ? "same" : "diff",
         SCIPprobdataGetIds(SCIPgetProbData(scip))[id1], SCIPprobdataGetIds(SCIPgetProbData(scip))[id2]);

      /* depending on the branching type select the correct left and right hand side for the linear constraint which
       * enforces this branching decision in the pricing problem MIP
       */
      if( type == SAME )
      {
         /* TODO: initialize the left hand side (lhs), the right hand side (rhs), and the variable bound coefficient
          *       (vbdcoef) for the case of "same" constraint" (the items are both in the packing or not)*/
         lhs = 0;
         rhs = 0;
         vbdcoef = -1;

      }
      else if( type == DIFFER )
      {
         /* TODO: initialize the left hand side (lhs), the right hand side (rhs), and the variable bound coefficient
          *       (vbdcoef) for the case of "differ" constraint" (the items are not together in a packing) */
         lhs = -SCIPinfinity(subscip);
         rhs = 1;
         vbdcoef = 1.;
      }
      else
      {
         SCIPerrorMessage("unknown constraint type <%d>\n, type");
         return SCIP_INVALIDDATA;
      }

      /* 
       * TODO: add linear (in that case a variable bound) constraint to pricing MIP depending on the branching type:
       *
       * - branching type SAME:  x1 = x2 <=> x1 - x2 = 0 <=> 0 <= x1 - x2 <= 0
       *
       * - branching type DIFFER:  x1 + x2 <= 1 <=> -inf <= x1 + x2 <= 1
       *
       */
      SCIPcreateConsVarbound(subscip,
            &vbcons, "vb", vars[id1], vars[id2], vbdcoef, lhs, rhs,
            TRUE, TRUE, TRUE, TRUE, TRUE, FALSE, FALSE, FALSE, FALSE, FALSE );
      
      SCIPaddCons(subscip, vbcons);

   }

   return SCIP_OKAY;
}

/** avoid generating columns which are fixed to zero; therefore add for each variable which is fixed to zero a
 *  corresponding logicor constraint to forbid this column
 *
 * @note variable which are fixed locally to zero should not be generated again by the pricing MIP
 */
static
SCIP_RETCODE addFixedVarsConss(
   SCIP*                 scip,               /**< SCIP data structure */
   SCIP*                 subscip,            /**< pricing SCIP data structure */
   SCIP_VAR**            vars,               /**< variable array of the subscip */
   SCIP_CONS**           conss,              /**< array of setppc constraint, for each item one */
   int                   nitems              /**< number of items */
   )
{
   SCIP_VAR** origvars;
   int norigvars;

   SCIP_CONS* cons;
   int* consids;
   int nconsids;
   int consid;
   int nvars;

   SCIP_VAR** logicorvars;
   SCIP_VAR* var;
   SCIP_VARDATA* vardata;
   SCIP_Bool needed;
   int nlogicorvars;

   int v;
   int c;
   int o;

   /* collect all variable which are currently existing */
   origvars = SCIPgetVars(scip);
   norigvars = SCIPgetNVars(scip);

   /* loop over all these variables and check if they are fixed to zero */
   for( v = 0; v < norigvars; ++v )
   {
      assert(SCIPvarGetType(origvars[v]) == SCIP_VARTYPE_BINARY);

      /* if the upper bound is smaller than 0.5 if follows due to the integrality that the binary variable is fixed to zero */
      if( SCIPvarGetUbLocal(origvars[v]) < 0.5 )
      {
         SCIPdebugMessage("variable <%s> glb=[%.15g,%.15g] loc=[%.15g,%.15g] is fixed to zero\n",
            SCIPvarGetName(origvars[v]), SCIPvarGetLbGlobal(origvars[v]), SCIPvarGetUbGlobal(origvars[v]),
            SCIPvarGetLbLocal(origvars[v]), SCIPvarGetUbLocal(origvars[v]) );

         /* coolect the constraints/items the variable belongs to */
         vardata = SCIPvarGetData(origvars[v]);
         nconsids = SCIPvardataGetNConsids(vardata);
         consids = SCIPvardataGetConsids(vardata);
         needed = TRUE;

         SCIP_CALL( SCIPallocBufferArray(subscip, &logicorvars, nitems) );
         nlogicorvars = 0;
         consid = consids[0];
         nvars = 0;

         /* loop over these items and create a linear (logicor) constraint which forbids this item combination in the
          * pricing problem; thereby check if this item combination is already forbidden
          */
         for( c = 0, o = 0; o < nitems && needed; ++o )
         {
            assert(o <= consid);
            cons = conss[o];

            if( SCIPconsIsEnabled(cons) )
            {
               assert( SCIPgetNFixedonesSetppc(scip, cons) == 0 );

               var = vars[nvars];
               nvars++;
               assert(var != NULL);

               if( o == consid )
               {
                  SCIP_CALL( SCIPgetNegatedVar(subscip, var, &var) );
               }

               logicorvars[nlogicorvars] = var;
               nlogicorvars++;
            }
            else if( o == consid )
               needed = FALSE;

            if( o == consid )
            {
               c++;
               if ( c == nconsids )
                  consid = nitems + 100;
               else
               {
                  assert(consid < consids[c]);
                  consid = consids[c];
               }
            }
         }

         if( needed )
         {
            SCIP_CALL( SCIPcreateConsBasicLogicor(subscip, &cons, SCIPvarGetName(origvars[v]), nlogicorvars, logicorvars) );
            SCIP_CALL( SCIPsetConsInitial(subscip, cons, FALSE) );

            SCIP_CALL( SCIPaddCons(subscip, cons) );
            SCIP_CALL( SCIPreleaseCons(subscip, &cons) );
         }

         SCIPfreeBufferArray(subscip, &logicorvars);
      }
   }

   return SCIP_OKAY;
}

/** initializes the pricing problem for the given capacity */
static
SCIP_RETCODE initPricing(
   SCIP*                 scip,               /**< SCIP data structure */
   SCIP_PRICERDATA*      pricerdata,         /**< pricer data */
   SCIP*                 subscip,            /**< pricing SCIP data structure */
   SCIP_VAR**            vars                /**< variable array for the items */
   )
{
   SCIP_CONS** conss;
   SCIP_CONS* cons;
   SCIP_VAR* var;
   SCIP_Longint* weights;
   SCIP_Longint capacity;
   SCIP_Real dual;

   int nitems;
   int nvars;
   int c;

   assert(SCIPgetStage(subscip) == SCIP_STAGE_PROBLEM);
   assert(pricerdata != NULL);

   nitems = pricerdata->nitems;
   conss = pricerdata->conss;
   weights = pricerdata->weights;
   capacity = pricerdata->capacity;
   nvars = 0;

   /* TODO: initialization of the local pricing problem 
    *   - create variables for the pricing problem and store them in the vars array
    *   - create knapsack constraint
    */

   SCIPcreateConsKnapsack(subscip, &cons, "capacity", 0,
      NULL, NULL, capacity, TRUE, TRUE, TRUE, TRUE, TRUE, FALSE, FALSE, FALSE,
      FALSE, FALSE);

   SCIPaddCons(subscip, cons);
   
   for(nvars=0; nvars<nitems;++nvars)
   {
      dual = SCIPgetDualsolSetppc(scip, conss[nvars]);

      SCIPcreateVar(subscip, &var, "var", 0.0, 1.0, dual,
            SCIP_VARTYPE_BINARY, TRUE, FALSE, NULL, NULL, NULL, NULL, NULL );

      SCIPaddVar(subscip, var);
      SCIPaddCoefKnapsack(subscip, cons, var, weights[nvars]);
      vars[nvars] = var;
   }


   /* add constraint of the branching decisions (Note that there are TODOs in this method) */
   SCIP_CALL( addBranchingDecisionConss(scip, subscip, vars, pricerdata->conshdlr) );
   
   /* avoid to generate columns which are fixed to zero */
   SCIP_CALL( addFixedVarsConss(scip, subscip, vars, conss, nitems) ); 

   return SCIP_OKAY;
}

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
      SCIPfreeMemoryArrayNull(scip, &pricerdata->ids);

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
   SCIP* subscip;
   SCIP_PRICERDATA* pricerdata;
   SCIP_CONS** conss;
   SCIP_VAR** vars;
   SCIP_SOL* sol;
   int* ids;

   int nitems;
   SCIP_Longint capacity;

   SCIP_Real timelimit;
   SCIP_Real memorylimit;

   assert(scip != NULL);
   assert(pricer != NULL);

   (*result) = SCIP_DIDNOTRUN;

   /* get the pricer data */
   pricerdata = SCIPpricerGetData(pricer);
   assert(pricerdata != NULL);

   capacity = pricerdata->capacity;
   conss = pricerdata->conss;
   ids = pricerdata->ids;
   nitems = pricerdata->nitems;

   /* get the remaining time and memory limit */
   SCIP_CALL( SCIPgetRealParam(scip, "limits/time", &timelimit) );
   if( !SCIPisInfinity(scip, timelimit) )
      timelimit -= SCIPgetSolvingTime(scip);
   SCIP_CALL( SCIPgetRealParam(scip, "limits/memory", &memorylimit) );
   if( !SCIPisInfinity(scip, memorylimit) )
      memorylimit -= SCIPgetMemUsed(scip)/1048576.0;

   /* initialize SCIP */
   SCIP_CALL( SCIPcreate(&subscip) );
   SCIP_CALL( SCIPincludeDefaultPlugins(subscip) );

   /* create problem in sub SCIP */
   SCIP_CALL( SCIPcreateProbBasic(subscip, "pricing") );
   SCIP_CALL( SCIPsetObjsense(subscip, SCIP_OBJSENSE_MAXIMIZE) );

   /* do not abort subproblem on CTRL-C */
   SCIP_CALL( SCIPsetBoolParam(subscip, "misc/catchctrlc", FALSE) );

   /* disable output to console */
   SCIP_CALL( SCIPsetIntParam(subscip, "display/verblevel", 0) );

   /* set time and memory limit */
   SCIP_CALL( SCIPsetRealParam(subscip, "limits/time", timelimit) );
   SCIP_CALL( SCIPsetRealParam(subscip, "limits/memory", memorylimit) );

   SCIP_CALL( SCIPallocMemoryArray(subscip, &vars, nitems) );

   SCIPdebugMessage("   nitems: %d capacity: %"SCIP_LONGINT_FORMAT"  \n", nitems, capacity);
   /* initialization of the local pricing problem;
    * note that there are TODOs in this method!
    */
   SCIP_CALL( initPricing(scip, pricerdata, subscip, vars) );

   SCIPdebugMessage("solve pricer problem\n");

   
   /* TODO: solve the pricing SCIP */
   SCIPsolve(subscip); 
   
   /* TODO: replace NULL with the  best solution of the pricing problem */
   sol = SCIPgetBestSol(subscip); 
      
   if( sol != NULL )
   {
      SCIP_Bool feasible;
         
      /* check if solution is feasible in original subSCIP */
      SCIP_CALL( SCIPcheckSolOrig(subscip, sol, &feasible, FALSE, FALSE ) );

      if( !feasible )
      {
         SCIPwarningMessage(scip, "solution in pricing problem (capacity <%d>) is infeasible\n", capacity); 
      }
      else
      {
         int* consids;
         char name[SCIP_MAXSTRLEN];
         int nconsids;
         int v;
         
         nconsids = 0;

         (void) SCIPsnprintf(name, SCIP_MAXSTRLEN, "items"); 

         /* buffer to store the constraint ids for the variable data */
         SCIP_CALL( SCIPallocBufferArray(scip, &consids, nitems) );

         /* TODO: evaluate solution of the pricing problem */
         int j;
         for(j=0;j<nitems;++j)
         {
            if( SCIPgetSolVal(subscip,sol,vars[j]) > 0.5 )
            {
               consids[nconsids] = j;
               nconsids++;
            }
         }


         /* TODO: replace FALSE with the check if we found a solution with negative reduced cost */
         if( SCIPisGT(scip,SCIPgetSolOrigObj(subscip, sol),1.0) )
         {
            SCIP_VAR* var;
            SCIP_VARDATA* vardata;

            SCIPdebug( SCIP_CALL( SCIPprintSol(subscip, sol, NULL, FALSE) ) );

            /* TODO: create variable data */
            SCIPvardataCreateBinpacking(scip, &vardata, consids, nconsids);

            /* TODO: create a variable */
            SCIPcreateVarBinpacking(scip, &var, "var", 1.0, FALSE, TRUE, vardata);

            /* TODO: add the new variable to the pricer store */
            SCIPaddPricedVar(scip, var, 1.0);
            
            /* change the upper bound of the binary variable to lazy since the upper bound is already enforced due to
             * the objective function the set covering constraint; the reason for doing that is to avoid the bound
             * of x <= 1 in the LP relaxation since this bound constraint would produce a dual variable which might have
             * a positive reduced cost
             */
            SCIP_CALL( SCIPchgVarUbLazy(scip, var, 1.0) );
            
            /* TODO: add the new variable to the corresponding set covering constraints */
            int c;
            for(c=0;c<nconsids;++c)   
            {
               SCIPaddCoefSetppc(scip, conss[consids[c]], var); 
            }
            
            /* TODO: release the new variable such that SCIP takes care of it */
            SCIPreleaseVar(scip, &var);
           
         }
         
         SCIPfreeBufferArray(scip, &consids);
      }
   }

   /* free pricer MIP */
   SCIPfreeMemoryArray(subscip, &vars);

   /* free sub SCIP */
   SCIP_CALL( SCIPfree(&subscip) );

   (*result) = SCIP_SUCCESS;

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

   pricerdata->conshdlr = SCIPfindConshdlr(scip, "samediff");
   assert(pricerdata->conshdlr != NULL);

   pricerdata->conss = NULL;
   pricerdata->weights = NULL;
   pricerdata->ids = NULL;
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
   int*                  ids,                /**< array of item ids */
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
   SCIP_CALL( SCIPduplicateMemoryArray(scip, &pricerdata->ids, ids, nitems) );

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
