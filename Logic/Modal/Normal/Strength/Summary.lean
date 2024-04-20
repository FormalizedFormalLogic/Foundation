import Logic.Modal.Normal.Strength.Geach

namespace LO.Modal.Normal

open LogicalStrong LogicalEquivalence

variable {β} [DecidableEq β] [Inhabited β]

local infix:80 (priority := high) " ≤ᴸ " => @LogicalStrong β
local infix:80 (priority := high) " <ᴸ " => @LogicalStrictStrong β
local infix:80 (priority := high) " =ᴸ " => @LogicalEquivalence β

example : 𝐊 ≤ᴸ 𝐊𝐁 := by aesop

example : 𝐊 ≤ᴸ 𝐊𝐃 := by aesop

example : 𝐊𝐃 ≤ᴸ 𝐊𝐓 := by aesop

example : 𝐊 ≤ᴸ 𝐊𝐓 := by trans 𝐊𝐃 <;> aesop;

example : 𝐊 ≤ᴸ 𝐊𝟒 := by aesop

example : 𝐊 ≤ᴸ 𝐊𝟓 := by aesop

example : 𝐊𝐓 ≤ᴸ 𝐒𝟒 := by aesop

example : 𝐊𝟒 ≤ᴸ 𝐒𝟒 := by aesop

example : 𝐒𝟒 ≤ᴸ 𝐒𝟒.𝟐 := by aesop

example : 𝐒𝟒 ≤ᴸ 𝐒𝟒.𝟑 := by aesop

example : 𝐒𝟒 ≤ᴸ 𝐒𝟒𝐆𝐫𝐳 := by aesop

example : 𝐒𝟒 ≤ᴸ 𝐒𝟓 := S4_S5

example : 𝐊 ≤ᴸ 𝐒𝟒 := by trans 𝐊𝟒 <;> aesop;

example : 𝐒𝟓 =ᴸ 𝐊𝐓𝟒𝐁 := by aesop;

example : 𝐊 ≤ᴸ 𝐆𝐋 := by aesop

end LO.Modal.Normal
