*! version 0.1.2  04oct2011
/*

REGO - R² decomposition with Shapley/Owen values
by Frank Huettner and Marco Sunder

Change log

	0.1.2 (04oct2011)
	- missing variable names in output table when variable list contained more then 244 characters: fixed 
	- "detail" can now be limited to certain groups
	- e(cmdline) shows actual input, not expanded variable list
	
	0.1.1 (29sep2011)
	- introduce option "noperc"
	- adjust bootstrap in case quantile*bsreps is integer
	
	0.1.0 (20sep2011)

*/


capture program drop rego 
capture program drop rego_table
capture program drop rego_bsoutput
capture program drop rego_error

// ********************************************************
//                INTERPRET THE USER'S INPUT
// ********************************************************

program define rego, eclass
version 9
mata: ver = 0.01 * stataversion()
mata: st_local("ver",strofreal(ver))
local ver = real("`ver'")
ereturn clear
syntax [anything] [if] [in] ///
[, Vce(string) Detail Noperc force Bsreps(integer 0) Level(cilevel)]

if (length(trim(itrim("`anything'"))) == 0) {
	rego_table
	exit
	}
local bsreps = real("`bsreps'")
tokenize `anything'
local cmdl `"rego `0'"'
local depvar `1'
macro shift
local rhs `"`*'"'
tsunab depvar: `depvar'
local regressors  ""	 
local nvarspergroup  ""

matrix __d = J(1,1,.)  // Owen values for a certain group?
matrix __q = J(1,1,.)  // Number of variables for a certain group?
local max__q = 0
local max__qd = 0

while (`:length local rhs' > 0) {
gettoken group rhs: rhs, parse("\")
if `"`group'"' != "\" {
	local thisdetail = strpos(`"`group'"',"(detail)")
	if (`thisdetail'>1 | strlen("`detail'")>0) local thisdetail = 1
	local group : subinstr local group "(detail)" "", all
	if (`thisdetail' == 1) {
		matrix __d = (__d \ 1)
		}
	else {
		matrix __d = (__d \ 0)
		}
	if (`ver' >= 11) {
		fvunab group: `group'
		}
	else {
		tsunab group: `group'
		}
	local nvtg : word count `group'
	local nvtgd = `nvtg' * `thisdetail'
	if (`nvtg' > `max__q') local max__q = `nvtg'
	if (`nvtgd' > `max__qd') local max__qd = `nvtgd'
	local regressors `"`regressors' `group'"'
	local nvarspergroup `"`nvarspergroup' `nvtg'"'
	matrix __q = (__q \ `nvtg')
	}		
}
matrix __d = __d[2..rowsof(__d),1]
matrix __q = __q[2..rowsof(__q),1]
if (strlen("`detail'") > 0) matrix __d = J(rowsof(__d),1,1)

if (rowsof(__q) == 1) { // classical Shapley case
	matrix __q = J(__q[1,1],1,1)
	matrix __d = J(rowsof(__q),1,0)
	}
local ngroups = rowsof(__q)
	
if (`bsreps' > 0 & `bsreps' < 100) {
	di as err "bsreps must be >= 100"
	rego_error
	}

local vceopt =""
if strlen("`vce'") > 0 {
	local vceopt = "vce(`vce')"
}


local nopercorig = "`noperc'"
if strlen("`noperc'") > 0 {
	local noperc = 1
	}
else {
	local noperc = 0
	}

if (`ver' >= 11) {
	local rc = 0
	capture _fv_check_depvar `depvar' `regressors'
	local rc = _rc
	if (`rc' == 198) {
		di as err "Factor variables not supported " _c
		di as err "(try -{help xi}- instead)"
		rego_error
	}
}
		
		
local toobig = 0
if (rowsof(__q) >= 13 | `max__qd' >= 13) {
	if (strlen("`force'") == 0) {
		local toobig = 1
		di as err "Problem too big for REGO ...proceeding with REGRESS instead"
		}
	}
	
local prefix = " "
if (`toobig' == 0) {
	local prefix = "quietly"
	}
	

// ********************************************************
//               OBTAIN OLS REGRESSION RESULTS
// ********************************************************

`prefix' regress `depvar' `regressors' `if' `in',`vceopt' 
if (e(ll)==.) {  // depvar probably included in regressors
	di as err "Numerical problems" 
	rego_error
	}
if (`toobig' == 1) {
	matrix drop __d __q
	exit
	}
tempvar _e_sample
generate `_e_sample' = e(sample)


// ********************************************************
//                CALCULATE OWEN/SHAPLEY VALUES
// ********************************************************	

mata: q = st_matrix("__q")
mata: d = st_matrix("__d")
mata: olsb = st_matrix("e(b)")
mata: rego_main("`depvar'",`"`regressors'"', ///
  "`_e_sample'",q,d,`noperc',olsb,`bsreps',`level')

	
// ********************************************************
//                      STORE RESULTS
// ********************************************************	

	matrix __olsb = e(b)
	local K = colsof(__olsb)
	local n = e(N)
	matrix __stdb      = J(1,`K',.)

	quietly summarize `depvar' if e(sample)
	local sdy = r(sd)
	local i = 1
	foreach j in `regressors' {
		quietly summarize `j' if e(sample)
		matrix __stdb[1,`i'] = __olsb[1,`i'] *  (r(sd)/`sdy')
		local i = `i' + 1	
		}

	local ovlab = ""
	local i = 1
	while (`i' <= wordcount("`regressors'")) {
		local ovlab = "`ovlab' OV`i'"
		local i = `i' + 1
		}
		
	local svlab = ""
	local i = 1
	while (`i' <= `ngroups') {
		local svlab = "`svlab' SV`i'"
		local i = `i' + 1
		}
		
	ereturn local cmd             = "rego"
	ereturn local regressors `"`regressors'"'
	ereturn matrix stdb           = __stdb
	ereturn matrix vars_per_group = __q
	ereturn matrix group_details  = __d
	ereturn local cmdline          `"`cmdl'"'

if (`bsreps' == 0) {
	matrix __percOV               = 100 * __OV / e(r2)
	matrix __percSV               = 100 * __SV / e(r2)
	matrix colnames __OV = `ovlab'
	matrix colnames __SV = `svlab'
	matrix colnames __percOV = `ovlab'
	matrix colnames __percSV = `svlab'	
	ereturn matrix shapley        = __SV
	ereturn matrix shapley_perc   = __percSV
	if (`max__qd' > 1)  {
		ereturn matrix owen       = __OV
		ereturn matrix owen_perc  = __percOV
		}
	else {
		matrix drop __OV
		matrix drop __percOV
		}
	ereturn scalar noperc = `noperc'
	rego_table
	}
	
else { // bootstrap

	local rlab = "CI_lower Median CI_upper"
	
	matrix rownames __OV_s = `rlab'
	matrix rownames __SV_s = `rlab'	
	matrix colnames __OV_s = `ovlab'
	matrix colnames __SV_s = `svlab'
	
	ereturn local cmd             = "rego_bootstrap"
	ereturn local cmdline           `"`cmdl'"'
	ereturn local level = `level'
	ereturn scalar noperc = `noperc'	
	
	if (`noperc' == 1) {
		if (`max__qd' > 1) ereturn matrix bs_owen = __OV_s
		ereturn matrix bs_shapley     = __SV_s
		}
	else {
		if (`max__qd' > 1) ereturn matrix bs_owen_perc   = __OV_s
		ereturn matrix bs_shapley_perc= __SV_s		
		}
	
	rego_bsoutput
	
	}

end // of rego



// ********************************************************
//                       SHOW RESULTS
// ********************************************************	

program define rego_table
mata: ver = 0.01 * stataversion()
mata: st_local("ver",strofreal(ver))
local ver = real("`ver'")



if (e(cmd) != "rego") {  // for replay of results
	di as err "last estimates not found"
	rego_error
	}


local noperc = e(noperc)
if (`noperc' == 1) {
	matrix __OVx = e(owen)		
	matrix __SVx = e(shapley)
	}
else {
	matrix __OVx = e(owen_perc)
	matrix __SVx = e(shapley_perc)
	}	
matrix __olsb         = e(b)	
matrix __stdb         = e(stdb)
matrix __d            = e(group_details)
matrix __q            = e(vars_per_group)
matrix __olsV         = e(V)
local K               = colsof(__olsb)
local regressors      `e(regressors)'
matrix __serr         = J(1,`K',0)	
matrix __pval         = J(1,`K',0)
matrix __nast         = J(1,`K',0)

local i = 1
while (`i' <= `K') {

	matrix __serr[1,`i'] = __olsV[`i',`i'] ^ 0.5
	
	local tratio = __olsb[1,`i'] / __serr[1,`i']
	local p=2*ttail(e(df_r),abs(__olsb[1,`i']/__serr[1,`i']))
	matrix __pval[1,`i'] = `p'
	matrix __nast[1,`i']=1*(`p'<0.1)+1*(`p'<0.05)+1*(`p'<0.01)
	local i = `i' + 1
	}

local i = 1
local max__d = 0
while (`i' <= rowsof(__d)) {
	if (__d[`i',1] > `max__d') local max__d = __d[`i',1]
	local i = `i' + 1
	}

local tabletype = 1             // display group only

if (`max__d' > 0) {
	local tabletype = 2         // display individual+group 
	}
		
if (rowsof(__q) == (colsof(__olsb)-1)) {
	local tabletype = 3   	    // traditional Shapley 
	}	
 
di as text " "
di as text "{hline 20}{c TT}{hline 57}"
di as text "Gr        Regressor {c |}       Coef.      " _c
di as text "Std.Err.   P>|t|" _c



if (`noperc' == 1) {
		if (`tabletype' == 1) {
			di as text "  Std.Coef.    Group R2"
			}
		if (`tabletype' == 2) {
			di as text "    Ind. R2    Group R2"
			}
		if (`tabletype' == 3) {
			di as text "  Std.Coef.  Shapley R2"
			}
	}
else {
		if (`tabletype' == 1) {
			di as text "  Std.Coef.   Group %R2"
			}
		if (`tabletype' == 2) {
			di as text "   Ind. %R2   Group %R2"
			}
		if (`tabletype' == 3) {
			di as text "  Std.Coef. Shapley %R2"
			}	
	}
	
di as text "{hline 20}{c +}{hline 57}"

local i = 1
local r = 1
local oldr = 0
while (`r' <= rowsof(__q)) {

	local contentr = __q[`r',1]
	local c = 1
	while (`c' <= `contentr') {
		if (`r' != `oldr') {
			di as result %2.0f `r' _c
			}
		else {
			di as text "  " _c
			}
				
	local asterstr = "   "
	if (__nast[1,`i']==1) {
		local asterstr = "*  "
		}
	if (__nast[1,`i']==2) {
		local asterstr = "** "
		}
	if (__nast[1,`i']==3) {
		local asterstr = "***"
		}
		
	di as text " " _c
	local vname : word `i' of `regressors'
	di as text %16s abbrev(("`vname'"),16) _c
	di as text " {c |}   " _c
	di as result %9.0g __olsb[1,`i'] " " _c
	di as result %3s "`asterstr'" " " _c
	di as result %9.0g __serr[1,`i']  "   " _c
	di as result %5.3f __pval[1,`i']  "    " _c
	if (`tabletype' == 1) {
		di as result %7.4f __stdb[1,`i'] "     " _c
		if (`r' != `oldr') {
			di as result %7.4f __SVx[1,`r']  
			}
		else {
			di as result "      " 
			}
		}				
	if (`tabletype' == 2) {
		if (__OVx[1,`i'] != .) {
			di as result %7.4f __OVx[1,`i'] "     " _c
			}
		else {
			di as result "            " _c
			}
		if (`r' != `oldr') {
			di as result %7.4f __SVx[1,`r']  
			}
		else {
			display as result "      " 
			}  	
		}							
	if (`tabletype' == 3) {
		di as result %7.4f __stdb[1,`i']   "     " _c
		di as result %7.4f __SVx[1,`i']   	
		}
		
	local c    = `c' + 1
	local i    = `i' + 1
	local oldr = `r'
	}
	local r = `r' + 1			
}
		
local asterstr = "   "  // for intercept term
if (__nast[1,`i']==1) {
	local asterstr = "*  "
	}
if (__nast[1,`i']==2) {
	local asterstr = "** "
	}
if (__nast[`i',1]==3) {
	local asterstr = "***"
	}						
		
di as text " - " _c 
di as text %16s abbrev("Intercept",16) " {c |}   " _c
di as result %9.0g __olsb[1,`i']    " " _c
di as result %3s "`asterstr'" " " _c
display as result %9.0g __serr[1,`i']   "   " _c
di as result %5.3f __pval[1,`i']  "     " 
	
di as text "{hline 20}{c +}{hline 57}"
di as text %19s "Observations" " {c |}   " _c
di as result %9.0f e(N)    

di as text %19s "Overall R2" " {c |}   " _c
di as result %9.5f e(r2)    
	
di as text %19s "Root MSE" " {c |}   " _c
di as result %9.0g e(rmse)    	

di as text %19s "F-stat. Model" " {c |}   " _c
local Fpval = Ftail(e(df_m),e(df_r),e(F))
local asterstr = "   "
if (`Fpval' < 0.1) {
	local asterstr = "*  "
	}
if (`Fpval' < 0.05) {
	local asterstr = "** "
	}	
if (`Fpval' < 0.01) {
	local asterstr = "***"
	}	
di as result %9.0g e(F)  " " _c
di as result %3s "`asterstr'" "             " _c
di as result %5.3f `Fpval'
	
di as text %19s "Log Likelihood" " {c |}   " _c
di as result %9.0g e(ll)     
		
di as text "{hline 20}{c BT}{hline 57}"	

matrix drop __olsb __stdb __q __d __olsV __OVx __SVx ///
            __serr __pval __nast 


end // of rego_table
	
	
// ********************************************************
//                  SHOW RESULTS (BOOTSTRAP)
// ********************************************************	
	
program define rego_bsoutput

local noperc     = e(noperc)

if (`noperc' == 1) {
	matrix __OV_s = e(bs_owen)
	matrix __SV_s = e(bs_shapley)
	}
else {
	matrix __OV_s    = e(bs_owen_perc)
	matrix __SV_s    = e(bs_shapley_perc)
	}

matrix __q       = e(vars_per_group)
matrix __d            = e(group_details)
local level      = e(level)
local regressors      `e(regressors)'

local i = 1
local max__d = 0
while (`i' <= rowsof(__d)) {
	if (__d[`i',1] > `max__d') local max__d = __d[`i',1]
	local i = `i' + 1
	}

local tabletype = 1             // display group only

if (`max__d' > 0) {
	local tabletype = 2         // display individual+group 
	}
		
if (rowsof(__q) == (colsof(__olsb)-1)) {
	local tabletype = 3   	    // traditional Shapley 
	}	

		
di ""
di as text "Bootstrap percentile confidence intervals for {bf:REGO}"
di as text "Approximate level of confidence: " _c
di as result %6.3g `level' " %"

if (`tabletype' == 1) {
	di as text "{hline 20}{c TT}{hline 28}"
	if (`noperc' == 1) {
		di as text "                    {c |}           Group R2        "
		}
	else {
		di as text "                    {c |}          Group %R2        "
		}
	di as text "Gr        Regressor {c |}   Median  CI lower   upper"
	di as text "{hline 20}{c +}{hline 28}"
	}
if (`tabletype' == 2) {
	di as text "{hline 20}{c TT}{hline 28}{c TT}{hline 28}"
	if (`noperc' == 1) {
		di as text "                    {c |}        Individual R2       {c |}           Group R2        "
		}
	else {
		di as text "                    {c |}       Individual %R2       {c |}          Group %R2        "
		}
	di as text "Gr        Regressor {c |}   Median  CI lower   upper {c |}   Median  CI lower   upper"
	di as text "{hline 20}{c +}{hline 28}{c +}{hline 28}"
	}
if (`tabletype' == 3) {
	di as text "{hline 20}{c TT}{hline 28}"
	if (`noperc' == 1) {
		di as text "                    {c |}          Shapley R2       "
		}
	else {
		di as text "                    {c |}         Shapley %R2       "
		}
	di as text "Gr        Regressor {c |}   Median  CI lower   upper"
	di as text "{hline 20}{c +}{hline 28}"
	}

local i = 1
local r = 1
local oldr = 0
while (`r' <= rowsof(__q)) {

	local contentr = __q[`r',1]
	local c = 1
	while (`c' <= `contentr') {
		if (`r' != `oldr') {
			di as result %2.0f `r' _c
			}
		else {
			di as text "  " _c
			}
				
	di as text " " _c
	local vname : word `i' of `regressors'
	di as text %16s abbrev(("`vname'"),16) _c
	di as text " {c |}" _c
	if (`tabletype' == 2) {	
		if (__OV_s[1,`i'] != .) {
			di as result %9.3f __OV_s[2,`i'] " " _c
			di as result %8.3f __OV_s[1,`i'] " " _c
			di as result %8.3f __OV_s[3,`i'] " " _c
			di as text "{c |}" _c
			}
		else {
			di as text "                            {c |}" _c
			}
		}
	if (`r' != `oldr') {
		di as result %9.3f __SV_s[2,`r'] " " _c
		di as result %8.3f __SV_s[1,`r'] " " _c
		di as result %8.3f __SV_s[3,`r'] " " _c	 
		}
	else {
			display as result "" _c
		}  	
	di as text ""
	local c    = `c' + 1
	local i    = `i' + 1
	local oldr = `r'
	}
	local r = `r' + 1			
}

if (`tabletype' == 2) {
	di as text "{hline 20}{c BT}{hline 28}{c BT}{hline 28}"
	}
else {
	di as text "{hline 20}{c BT}{hline 28}"
	}
	
matrix drop __q __d __olsb __SV_s __OV_s
end	
	
	
// ********************************************************
//                        FUNCTIONS
// ********************************************************	

	
program define rego_error	// turn command history red
	ereturn clear
	exit 101
end	
	
mata:

function rego_main(name_y,name_x,dsam,q,d,noperc,olsb,bsreps,conflevel)
{
	// Tell MATA where the data are, 
	// but don't duplicate them in memory
	// Note: using time-series operators casuses error in 
	//   STATA 9 but not in STATA 11 (differences in st_view)


	
	if (bsreps == 0)            
		{
			X       = J(0,0,.)
			Y       = J(0,0,.)
			st_view(X,.,tokens(name_x), tokens(dsam))
			st_view(Y,.,tokens(name_y), tokens(dsam))
			maxrep  = 1
		}
	else                        
		{
			display(" ")
			origX   = J(0,0,.)
			origY   = J(0,0,.)
			st_view(origX,.,tokens(name_x), tokens(dsam))
			st_view(origY,.,tokens(name_y), tokens(dsam))
			X       = origX
			Y       = origY
			maxrep  = bsreps
			displayas("text") 
			printf("       {it:Bootstrapping} \n          ")
		}
		
	obs     = rows(X)
	k       = cols(X)	

	if (k < 2)
		{
		  displayas("err") 
		  printf("not enough regressors\n")
		  stata("rego_error")
		}	

	if (rank(X) < k)
		{
		  displayas("err") 
		  printf("multicollinearity\n")
		  stata("rego_error")
		}
		
	if (cols(olsb)-1 != k)
		{
		  displayas("err") 
		  printf("dependent variable confusion\n")
		  stata("rego_error")
		}	
		
	// Translation matrix groups (rows) -> variables
			
	Q = J(rows(q),sum(q),0)	 
	for (i=1; i<=rows(q); i++)
		{
			Q[i,sum(q[1..i])-q[i]+1..sum(q[1..i])] = ///
				J(1,q[i],1)
		}
		
	ngroups	= rows(q)

	if (bsreps != 0)  // initialize bootstrap results matrices
		{
			bs_r2   = J(bsreps,1,.)
			bs_OV   = J(bsreps,cols(origX),.)
			bs_SV   = J(bsreps,rows(q),.)
		}	
	
for (rep = 1; rep <= maxrep; rep++)	
	{
	
		if (bsreps != 0)  // create bootstrap sample
			{

				bs_rows = 1 :+ floor(obs:*uniform(obs,1))
				X       = J(0,cols(origX),.)
				Y       = J(0,1,.)	 
				for (i=1; i<= rows(bs_rows); i++)
					{
						X = (X \ origX[bs_rows[i],] )
						Y = (Y \ origY[bs_rows[i],] )
					}	
			}
	
	// Covariances for faster computation of R2 

	Sxx = cov_xx(X)   
	Sxy = cov_xy(X,Y)
	syy = (obs-1)^(-1) * sum((Y :- (sum(Y)/obs)) :^(2)) 

	// Initialize results vectors	

	OV = J(1,k,.)       // Owen values for individual variables
	SV = J(1,ngroups,.) // Shapley values for groups

	// Combinations of groups 
	C = binary_comb(ngroups)

	// Line sequence (by rowsum in C)	
	L = pascal_list(ngroups):+1     

	// Begin iteration over groups

	for (g=1; g<=ngroups; g++)
	{
	
		showdet = d[g,1]
		
		// matrix D: combinations of group g variables, 
		//    all other variables set to 1		
						
		if (showdet != 0) 
			{
				inset = binary_comb(q[g])

			}
		else
			{
				inset = ( J(1,q[g],0) \ J(1,q[g],1) )
			}
		
		D = J(rows(inset),k,1)	
		D[,sum(q[1..g])-q[g]+1..sum(q[1..g])] = inset

		
		// External game:
			
		VEXT = J(rows(D),1,0)	// recursive values
		for (j=1; j<=rows(VEXT); j++)
			{		
			E = C * Q :* D[j,]	 
			// E: combinations of groups for a 
			// certain set of group g variables
			POT = J(rows(E),1,.) 
			for (jj=1; jj<=rows(L); jj++)
				{
					Ljj = L[jj]
					r2  = calculate_r2(Sxx,Sxy,syy,E[Ljj,])
					T   = sum(C[Ljj,])
					pp  = 0
					if (T > 0)
						{
							compl = comparelines(C[Ljj,],Ljj)
							for (jjj=1; jjj<=rows(compl); jjj++)
								{
									pp = pp + POT[compl[jjj]]
								}
							POT[Ljj] = (r2 + pp) / T
						}
					else
						{
							POT[Ljj] = 0
						}
				}
			VEXT[j]=POT[rows(POT)]-POT[rows(POT)-2^(ngroups-g)]
			}
			
		// Internal game:
			
		Dn  = D[,sum(q[1..g])-q[g]+1..sum(q[1..g])]
		
		if (showdet != 0) 
		{
			LL  = pascal_list(q[g]):+1		
			// LL: index to rows of Dn by ascending row sum
			
			POT = J(rows(LL),1,0)			

			for (j=1; j<= rows(POT); j++)
				{
					LLj = LL[j]				
					T   = sum(Dn[LLj,])
					pp  = 0
					if (T > 0)
						{
							compl = comparelines(Dn[LLj,],LLj)
							for (jj=1; jj<=rows(compl); jj++)
								{
									pp = pp + POT[compl[jj]]
								}
							POT[LLj] = (VEXT[LLj] + pp) / T
						}
					else
						{
							POT[LLj] = VEXT[LLj]
						}
				}

			for (i=1; i <= q[g]; i++)
				{
					dP=POT[rows(POT)]-POT[rows(POT)-2^(q[g]-i)]
					OV[sum(q[1..g])-q[g]+i] = dP
				}
				
			SV[g] = sum(OV[sum(q[1..g])-q[g]+1..sum(q[1..g])])
			
		} // end showdet != 0
			
		else
		{
			SV[g] = VEXT[2] - VEXT[1]  
		}
			
	}   // end iteration over groups

	if (bsreps != 0)
		{
			bs_r2[rep,1] = ///
			    calculate_r2(Sxx,Sxy,syy,J(1,cols(X),1))
			bs_OV[rep,] = OV
			bs_SV[rep,] = SV
			
			if (mod(rep,100)==0) 
				{
					displayas("input") // add dot
					printf(".")
					displayflush() 
				}
			if (mod(rep,1000)==0)
				{
					displayas("text") 
					printf("%8.0f\n          ", rep)
					displayflush()					
				}
			
		}
	
}	    // end of replication
 
	st_matrix("__q",q) // q may have been updated by Mata
	
	if (bsreps == 0)
		{
			st_matrix("__OV",OV)
			st_matrix("__SV",SV)
		}
	else
		{ 
			OV_s = J(3,cols(bs_OV),.)
			SV_s = J(3,cols(bs_SV),.)
			alpha = (1-conflevel/100)/2
			
			for (i = 1; i <= cols(bs_OV); i++)
				{
				    if (noperc == 0)
						{
							temp = (bs_OV[,i] :/ bs_r2) * 100
							temp = sort(temp,1)						
						}
					else
						{
							temp = bs_OV[,i]
							temp = sort(temp,1)								
						}
					for (j=1; j<=3; j++)
						{
							if (j==1) quant = alpha
							if (j==2) quant = 0.5
							if (j==3) quant = 1-alpha
							index = nquantile(bsreps,quant)
							if (index-floor(index)> 0.001)
								{
									OV_s[j,i] = 0.5 * (temp[floor(index)] + temp[floor(index+1)])
								}
							else
								{
									OV_s[j,i] = temp[floor(index)]
								}
						}
				}
			
			for (i = 1; i <= cols(bs_SV); i++)
				{
				    if (noperc == 0)
						{
							temp = (bs_SV[,i] :/ bs_r2) * 100
							temp = sort(temp,1)						
						}
					else
						{
							temp = bs_SV[,i]
							temp = sort(temp,1)								
						}	
					for (j=1; j<=3; j++)
						{
							if (j==1) quant = alpha
							if (j==2) quant = 0.5
							if (j==3) quant = 1-alpha
							index = nquantile(bsreps,quant)
							if (index-floor(index)> 0.001)
								{
									SV_s[j,i] = 0.5 * (temp[floor(index)] + temp[floor(index+1)])
								}
							else
								{
									SV_s[j,i] = temp[floor(index)]
								}
						}						
				}		
			
			st_matrix("__SV_s",SV_s)	
			st_matrix("__OV_s",OV_s)
		}

}  // end of function  



function select1(M,a) // "select" unavailable in Stata 9 
{
	V = J(0,cols(M),.)
	for (i=1; i <= rows(M); i++)
		{
			if (a[i] != 0)
				{
					V = (V \ M[i,])
				}
		}
	return(V)
}


function cov_xx(X)   // covariance matrix
{
	k   = cols(X)
	obs = rows(X)
	Sxx = J(k,k,.)
	adj = (obs-1)^(-1)
	for (i=1; i<=k; i++) 
		{
			dx_i = X[,i] :- (sum(X[,i])/obs)
			for (j=1; j<=i; j++) 
				{
					dx_j 		= X[,j] :- (sum(X[,j])/obs)
					dx_i_dx_j 	= dx_i :* dx_j
					cov 		= adj * sum(dx_i_dx_j)
					Sxx[i,j] 	= cov
					Sxx[j,i] 	= cov
				}		
		}	
	return(Sxx)
}

function cov_xy(X,Y)   // covariance vector
{
	k   = cols(X)
	Sxy = J(k,1,.)
	obs = rows(X)
	adj = (obs-1)^(-1)
	dy  = Y :- (sum(Y)/obs) 
	for (i=1; i<=k; i++) 
		{
			Sxy[i,1] 	= adj * sum((X[,i] :- (sum(X[,i])/obs)) :* dy)
		}
	return(Sxy)
}

function calculate_r2(Sxx,Sxy,syy,z)   // calculate R-squared based on covariances
{
	Stt =  select1(Sxx  , z')
	Stt = (select1(Stt' , z'))'
	Sty =  select1(Sxy  , z')
	r2  = (Sty' * invsym(Stt) * Sty) / syy
	return(r2)
}

function makebinary(d,slots)   // convert decimal number to binary vector
{
	B = J(1,slots,0)
	i = 0
	while (d > 0)
		{
			r = mod(d,2)
			d = (d-r)/2
			B[slots-i] = r
			i = i + 1
		}
	return(B)
}

function binary_comb(a)   // generate all combinations of zeros and ones
{
	G = J(2^a,a,.)
	for (i=0; i < 2^a ; i++)
		{
			j = i
			G[1+i,] = makebinary(j,a)
		}
	return(G)
}

function pascal_list(n)
{ 
	b = 2  								// set b = 10 for vector in boolean coordinates
	workList = ( 0, 1, b, b + 1 )		// start with row 4 (row 3 given)
	pascalRow = ( 1, 2, 1 ) 

		for( m=4; m<=n+1; m++)  		// run down the Pascal triangle
		{
			pascalRowNext = ( 1 )
			workListNext = (0, b:^( 0..(m-2) ))
			posIndex = 2
			for( k=2; k<m; k++) 		// run right within Pascal triangle row m
			{
				// generate the (m-1) over (k-1) entry in the next row of the Pascal triangle
				pascalRowNext = ( pascalRowNext, pascalRow[k-1] + pascalRow[k] ) 		
			}									

			for( k=2; k<m-1; k++) 		// run right within Pascal triangle row m
			{
				// add k-out-of-(m-1)-sets from (k-1)-out-of-(m-2)-sets adding element (m-1)	
				posIndexEnd = posIndex + pascalRow[k]-1
				workListNext = ( workListNext, workList[posIndex..posIndexEnd] :+ (b^(m-2)) ) 	

				posIndex = posIndex + pascalRow[k]
				posIndexEnd = posIndex + pascalRow[k+1]-1

				// add k-out-of-(m-1)-sets from k-out-of-(m-2)-sets
				workListNext = ( workListNext, workList[posIndex..posIndexEnd] ) 	
			}
			pascalRow = ( pascalRowNext, 1 )				// add the last entry in row m				
			workList = ( workListNext, (b^(m-1)-1)/(b-1) )	// add full m-set
		}
	return(workList[1..2^n]')	
} 

function comparelines(bincode,linenumber)	// vector of line numbers where one "1" is replaced by "0"
{
	v=J(0,1,.)
	groups = cols(bincode)
	for(a=1; a<=groups; a++)
		{
			if (bincode[1,groups+1-a] != 0)
				{
					nextline = linenumber-2^(a-1)
					v = (v \ nextline)
				}
		}
	return(v)
}

function nquantile(n,a)
{
	if (round(ceil(n*a)-n*a,0.000001) != 0)
		{
			res = ceil(n*a)
		}
	else
		{
			res = 0.5*(n*a + (n*a+1))
		}
	return(res)
}

end
exit
