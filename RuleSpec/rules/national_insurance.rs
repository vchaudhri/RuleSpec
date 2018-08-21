if (employment_status = employee)
 national_insurance_class = class1
if (employee_category = "A")
  if ((weekly_income < 162) or (monthly_income < 702))
 national_insurance_employee_rate[1] = 0
 national_insurance_employer_rate = 0
 else if ((weekly_income > 162 and weekly_income <= 892) or 
(monthly_income > 702 and monthly_income <= 3163))
 national_insurance_employee_rate[2] = 12%
 national_insurance_employer_rate = 13.8%
 else if ((weekly_income > 892) or (monthly_income > 3863))
  national_insurance_employee_rate[3] = 2%
  national_insurance_employer_rate = 13.8%
else if (employee_category = "B") # married women or widows
  if ((weekly_income < 162) or (monthly_income < 702))
 national_insurance_employee_rate[1] = 0
 national_insurance_employer_rate = 0
  else if ((weekly_income > 162 and weekly_income <= 892) or 
(monthly_income > 702 and monthly_income <= 3163))
 national_insurance_employee_rate[2] = 5.85%
 national_insurance_employer_rate = 13.8%
 else if ((weekly_income > 892) or (monthly_income > 3863))
   national_insurance_employee_rate[3] = 2%
   national_insurance_employer_rate = 13.8%
else if (employee_category = "C") # employees over state pension age
 if ((weekly_income < 162) or (monthly_income < 702))
   national_insurance_employee_rate[1] = undefined
   national_insurance_employee_rate[2] = undefined
   national_insurance_employee_rate[3] = undefined
 if ((weekly_income > 162) or (monthly_income > 702)
   national_insurance_employer_rate = 13.8%
else if (employee_category = "J") # who can defer or are paying elsewhere
 if ((weekly_income < 162) or (monthly_income < 702))
   national_insurance_employee_rate[1] = 0
   national_insurance_employer_rate = 0
 else if ((weekly_income > 162 and weekly_income <= 892) or (monthly_income > 702 and monthly_income <= 3163))
   national_insurance_employee_rate[2] = 12%
   national_insurance_employer_rate = 13.8%
 else if ((weekly_income > 892) or (monthly_income > 3863))
   national_insurance_employee_rate[3] = 2%
   national_insurance_employer_rate = 13.8%
else if (employee_category = "H") # apprentice under age of 25
   if ((weekly_income < 162) or (monthly_income < 702))
     national_insurance_employee_rate[1] = 0
     national_insurance_employer_rate = 0
   else if ((weekly_income > 162 and weekly_income <= 892) or (monthly_income > 702 and monthly_income <= 3163))
     national_insurance_employee_rate[2] = 2%
     national_insurance_employer_rate = 0
   else if ((weekly_income > 892) or (monthly_income > 3863))
     national_insurance_employee_rate[3] = 2%
     national_insurance_employer_rate = 13.8%
else if (employee_category = "M") # employees under the age of 21
  if ((weekly_income < 162) or (monthly_income < 702))
    national_insurance_employee_rate[1] = 0
    national_insurance_employer_rate = 0
  else if ((weekly_income > 162 and weekly_income <= 892) or (monthly_income > 702 and monthly_income <= 3163))
    national_insurance_employee_rate[2] = 12%
    national_insurance_employer_rate = 0
  else if ((weekly_income > 892) or (monthly_income > 3863))
    national_insurance_employee_rate[3] = 2%
    national_insurance_employer_rate = 13.8%
else if (employee_category = "Z")ï¿½ï¿½ # employees under the age of 21 who can defer national insurance as they are paying it elsewhere
   if ((weekly_income < 162) or (monthly_income < 702))
     national_insurance_employee_rate[1] = 0
     national_insurance_employer_rate = 0
   else if ((weekly_income > 162 and weekly_income <= 892) or (monthly_income > 702 and monthly_income <= 3163))
     national_insurance_employee_rate[2] = 2%
     national_insurance_employer_rate = 0
   else if ((weekly_income > 892) or (monthly_income > 3863))
     national_insurance_employee_rate[3] = 2%
     national_insurance_employer_rate = 13.8%
else if (employee_category = "X") # employees who do not have to pay, e.g., under 16 years of age
    national_insurance_employee_rate[1] = 0
    national_insurance_employee_rate[2] = 0
    national_insurance_employee_rate[3] = 0
    national_insurance_employer_rate = 0


if (employment_status = employee) and (national_insurance_employee_rate[1] <> undefined)
  if ((weekly_income < 162) or (monthly_income < 702))
    national_insurance_employee_amt = 0
  else if ((weekly_income > 162 and weekly_income <= 892) or (monthly_income > 702 and monthly_income <= 3163))
    national_insurance_employee_amt = (weekly_income - 162) * 
    national_insurance_employee_rate[2]
    national_insurance_employer_amt = (weekly_income - 162) * 
    national_insurance_employer_rate[2]
  else if ((weekly_income > 892) or (monthly_income > 3863))
    national_insurance_employee_amt = ( 892 * 
    national_insurance_employee_rate[2]) + ( weekly_income - 892 ) * 
    national_insurance_employee_rate[3]
    national_insurance_employer_amt = ( 892 * national_insurance_employer_rate[2]) + ( weekly_income - 892 ) * national_insurance_employer_rate[3]


if (employement_status = self-employed)
  ### fisherman
  if (employment_title = "Fisherman")
    national_insurance_class = class2
    national_insurance_self_employed_rate[1] = 3.5/week
  ###
  ### landlord
  else if (employment_title = "Landlord")
    if (annual_profit < 5965) #choice of class2/3 voluntary contribution
      if (voluntary contribution_choice = class2)
        national_insurance_class = class2
        national_insurance_self_employed_rate[1] = 2.95/week
      else if (voluntary contribution_choice = class3)
        national_insurance_class = class3
        national_insurance_self_employed_rate[1] = 14.65/week
    else
      national_insurance_self_employed_rate[1] = 2.95/week
      national_insurance_self_employed_rate[2] = 9%
      national_insurance_self_employed_rate[3] = 2%
      if (annual_profit < 8424)
        national_insurance_class = class2
      else
        national_insurance_class = class4
  ###
  else if (annual_profit < 6205)
    national_insurance_self_employed_rate[1] = 0
    national_insurance_self_employed_rate[2] = 0
  else if (annual_profit > 6205) and (annual_profit < 8424)
    national_insurance_class = class2
    national_insurance_self_employed_rate[1] = 2.95/week
    national_insurance_self_employed_amt = national_insurance_self_employed_rate[1] * (annual_profit - 6205)
  else if (annual_profit > 8424)
    national_insurance_class = class4
    national_insurance_self_employed_rate[1] = 2.95/week
    national_insurance_self_employed_rate[2] = 9%
    national_insurance_self_employed_rate[3] = 2%

  if (annual_profit < 56350)
    national_insurance_self_employed_amt = national_insurance_self_employed_rate[1] * (annual_profit - 6205) + national_insurance_self_employed_rate[2] * (annual_profit - 8424)
  else 
    national_insurance_self_employed_amt = national_insurance_self_employed_rate[1] * (annual_profit - 6205) + national_insurance_self_employed_rate[2] * (annual_profit - 8424) + national_insurance_self_employed_rate[3] * (annual_profit - 56350)


if (employment_status = director)
  if (pay_method = annual)
    weekly_pay = annual_pay / 52
