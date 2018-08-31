
if (employment_status == employee) and (R1 <> 'undefined') then 
   if (weekly_income < 162) then  national_insurance_employee_amt = 0 endif
   if (weekly_income > 162) and (weekly_income <= 892) then national_insurance_employee_amt = (weekly_income - 162) * R2 endif
   if (weekly_income > 892) then national_insurance_employee_amt = (( 892 - 162 ) * R2) + ( weekly_income - 892 ) * R3 endif
endif

### fisherman
if (employement_status == 'self_employed') and (employment_title == 'Fisherman')  then
    WR1 = 3.5
endif

### landlord
if (employment_status == 'self_employed') and (employment_title == 'Landlord') then
    #choice of class2/3 voluntary contribution
    if (annual_profit < 5965) then
      if (voluntary_contribution_choice == class2) then
        national_insurance_class = class2
        WR1  = 2.95
      else if (voluntary_contribution_choice == class3) then
        national_insurance_class = class3
        WR1 = 14.65
      endif
      endif
    else
      WR1 = 2.95
      R2 = 0.09
      R3 = 0.02
      if (annual_profit < 8424) then
        national_insurance_class = class2
      else
        national_insurance_class = class4
      endif
   endif
endif

if (employment_status == 'self_employed') and (employment_title <> 'Landlord') and (employment_title <> 'Fisherman') then
    if (annual_profit < 6205) then
       R1 = 0
       R2 = 0
   else if (annual_profit < 8424) then
    national_insurance_class = class2
    WR1 = 2.95
  else if (annual_profit > 8424) then
    national_insurance_class = class4
    WR1 = 2.95
    R2 = 0.09
    R3 = 0.02
  endif
endif
endif
endif
  
