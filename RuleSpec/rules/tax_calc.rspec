# Issues
# Reporting requirements
# Aligning the results to manual tables
# Test Data
# Unless rounded, all computations should be carried out to four decimal places


# C[1], C[2], C[3] - cumulative bandwidths
C[1] = 0
C[2] = 33500
C[3] = 150000

# c[1], c[2], c[3] - cumulative bandwidth / 52
c[0] = 0
c[1] =  C[1] / 52 
c[2] =  C[2] / 52
c[3] =  C[3] / 52 

# R[1], R[2], R[3], R[4] - Tax Rates
R[1] = 0.10
R[2] = 0.20
R[3] = 0.40
R[4] = 0.45

# M - Max rate - maximum percentage tax deductible
M = 0.5

# K[1], K[2], K[3] - Cumulative annual tax
K[1] = 0
K[2] = 6700
K[3] = 53300

# k[0], k[1], k[2], k[3] - Cumulative annual tax / 52
k[0] = 0

# Stage 1
# P[n] - cumulative pay for week n
# p[n] - pay for the current week

P[n]=P[nm1] + p[n]

# Stage 2
# a1 - free pay or additional pay for week 1
# code - numberic part of the income code

if (code == 0) then
   a1 = 0
else 
     a1  =  ((5000 / 52 * (code - 1) div 500) + 
       	   	      (((code - 1) mod 500 + 1) * 10 + 9) / 52)
endif

# prefix_code - prefix of the income code
# suffix_code - suffix of the income code
# U[n] - Taxable pay up to and including week n before applying the rounding rules


if ( suffix_code) then
   U[n] = P[n]  - n * a1
else if ( prefix_code == "k") or (prefix_code == "SK") then
    U[n] = P[n] + n * a1
    endif
 endif

# L[n] - Tax liability up to and including the week n
if (suffix_code) and (U[n] <= 0 )  then
    L[n]  = 0
endif

# Stage (3) 
# T(n] - Taxable pay up to and including week n after applying the rounding rules
# U(n] is used for choosing the correct formula, and then rounded down to T(n] for calculation purposes.
# R(1], R(2], R(3] are tax rates

T[n] = U[n]

if (cumulative_suffix_code) or (cumulative_prefix_code == "S") or (prefix_code == "SK") then
   if (U[n]  < C[1]) then
       L[n] = k[0] + (T[n]  - c[0]) * R[1]
   else if (U[n]  < C[2]) then
      L[n]  = k[1] + (T[n] - c[1]) * R[2]
   else if (U[n]  < C[3]) then
      L[n]  = k[2] + (T[n]  - c[2]) * R[3]
   else
      L[n]  = k[3] + (T[n]  - c[3]) * R[4]
   endif
endif
endif
endif

if  (cumulative_code == "BR") or (cumulative_code == "SBR") then
   L[n] = T[n] * R2
endif

if (cumulative_prefix_code == "D0") then
   L[n] = T[n] * R3
endif

if (cumulative_prefix_code == "D1") then
   L[n] = T[n] * R4
endif

if ( cumulative_code == "NT") then
   L[n] = 0
endif

if (cumulative_code == "NT") then  L[n] = 0 endif

#L[n] = round_down(L[n], p)

# Stage 4
# I(n] - Tax deductible or refundable in week n
# pbik - payroll benefits in kind for week n

if ((L[n] > 0) and (L[n] < M)) or ((L[n] < 0) and (n > 1)) then
   I[n] = L[n]  - L[nm1]
else if (L[n] < 0) and (n == 1) then
   I[n] = 0
else
   I[n] = M * (p[n] - pbik[n])
   L[n]  = L[nm1] + I[n]
endif
endif


# Week 1 Basis computation

if (week1_basis) and (((prefix_code == "k") or (prefix_code == "SK")) or (suffix_code)) then
   if ( suffix_code) then
      U[n] = p[n] -  a1
   else if ((prefix_code == "k") or (prefix_code == "SK")) then
      Un =  p[n] +  a1
      	endif
   endif
endif

if (week1_basis) then
   if (L[n] > 0) and (L[n] < M) then
      I[n] = L[n]
   else if (L[n] < 0) then 
      I[n] = 0
   else
	I[n] = M * (p[n] - pbik[n])
  	 L[n]  = I[n]
	endif
   endif
endif