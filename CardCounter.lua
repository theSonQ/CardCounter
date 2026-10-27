-- licznik zdobytych kart potworow dla Runes of Magic
-- Dziala przez skanowanie plecaka (GetBagCount / GetBagItemInfo) i szukanie
-- przedmiotow, ktorych nazwa zawiera wzorzec (domyslnie "Karta").
-- Skanowanie jest wywolywane po evencie PLAYER_BAG_CHANGED / BAG_ITEM_UPDATE
-- oraz dodatkowo co ok. 1.5s jako zabezpieczenie (OnUpdate), gdyby eventy
-- plecaka nie odpalily sie w oczekiwany sposob.
-- archiwum sesji jak w KillCounterze - biezaca sesja jest zapisywana
-- w SavedVariables przy kazdej karcie, poprzednie sesje trafiaja do archiwum
-- z przewijana lista i strzalkami wyboru sesji.
-- ikona przy minimapie nie wypada poza ekran.
--  metoda "diff plecaka", nie zaklada nic o niepotwierdzonych
-- funkcjach Kompendium Kart (LuaFunc_GetCardInfo itp.).

local CardCounter = { version = "1.7" }
_G.CardCounter = CardCounter

CardCounterSet = CardCounterSet or {}

local active
local ready = false
local bagSnapshot = nil -- nil = jeszcze nie zbudowano bazy (pierwszy skan)
local lastScan = 0
local SCAN_MIN_INTERVAL = 0.5
local lastPoll = 0
local POLL_INTERVAL = 1.5
local miniDragging = false
local historyOpen = false
local ROW_COUNT = 12
local historyIndex = 0
local offset = 0
local displayRows = {}
local displayKinds = 0
local listDirty = true
local scrollUpdating = false

local function Print(msg)
	DEFAULT_CHAT_FRAME:AddMessage("|cff55DDFF[Karty]|r "..msg)
end

local defaults = {
	total = 0,
	cards = {},
	pattern = "Karta",
	sessions = {},
	chat = false,
	debug = false,
	hasPos = false,
	posPoint = "CENTER",
	posRel = "CENTER",
	posX = 160,
	posY = 0,
	btnHasPos = false,
	btnX = 0,
	btnY = 0,
	btnNorm = 0,
}

-- Pozycja ikony przy minimapie zapisana jako offset od srodka
-- MinimapViewFrame. GetLeft()/GetTop() zwracaja bezwzgledne
-- wspolrzedne pikseli ekranu, wiec zapis jedynie odejmuje je
-- od srodka minimapy; po wczytaniu przypinamy z powrotem.
-- Dziala to tak samo po zmianie rozdzielczosci i skali UI.
local function MinimapCenterXY()
	local mf = _G["MinimapViewFrame"]
	if mf and mf.GetLeft then
		local l = tonumber(mf:GetLeft()) or 0
		local t = tonumber(mf:GetTop()) or 0
		local w = tonumber(mf.GetWidth and mf:GetWidth()) or 160
		local h = tonumber(mf.GetHeight and mf:GetHeight()) or 160
		return l + w / 2, t + h / 2, true
	end
	return nil, nil, false
end

local function RestoreMinimapButton()
	local set = CardCounterSet
	if not set.btnHasPos then return end
	local btn = _G["CardCounterMinimapButton"]
	if not btn then return end
	-- zapis w offsetach od srodka minimapy (srodek ikony),
	-- wiec przy przywracaniu cofamy o polowe rozmiaru ikony.
	if set.btnNorm == 2 then
		local dx = tonumber(set.btnX) or 0
		local dy = tonumber(set.btnY) or 0
		-- ochrona: offset wiekszy niz ekran znaczy uszkodzony zapis
		local w = tonumber(GetScreenWidth()) or 1024
		local h = tonumber(GetScreenHeight()) or 768
		if math.abs(dx) > w or math.abs(dy) > h then
			set.btnHasPos = false
			btn:ClearAllAnchors()
			btn:SetAnchor("CENTER", "CENTER", "MinimapViewFrame", -80, -14)
			return
		end
		btn:ClearAllAnchors()
		btn:SetAnchor("CENTER", "CENTER", "MinimapViewFrame", dx, dy)
		return
	end
	-- stary zapis - przelicz na offset i przypnij z powrotem
	local w = tonumber(GetScreenWidth()) or 1024
	local h = tonumber(GetScreenHeight()) or 768
	local x, y
	if set.btnNorm == 1 then
		x = (tonumber(set.btnX) or 0) * (w / 1024)
		y = (tonumber(set.btnY) or 0) * (h / 768)
	else
		x = tonumber(set.btnX) or 0
		y = tonumber(set.btnY) or 0
	end
	if x < -100 or x > w + 50 or y < -100 or y > h + 50 then
		set.btnHasPos = false
		btn:ClearAllAnchors()
		btn:SetAnchor("CENTER", "CENTER", "MinimapViewFrame", -80, -14)
		return
	end
	set.btnHasPos = false -- pierwsze przeciagniecie po aktualizacji
	btn:ClearAllAnchors() -- zapisze nowy format
	btn:SetAnchor("CENTER", "CENTER", "MinimapViewFrame", -80, -14)
end

-- bez walidacji wzgledem rozmiaru ekranu - powodowala odrzucanie
-- legalnych pozycji na 4K.
local function RestorePos(frame, point, rel, x, y)
	local px, py = tonumber(x), tonumber(y)
	if not px or not py or not point or not rel then return false end
	frame:ClearAllAnchors()
	frame:SetAnchor(point, rel, "UIParent", px, py)
	return true
end

local function CurStamp()
	if os and os.date then
		local ok, value = pcall(os.date, "%Y-%m-%d %H:%M")
		if ok and type(value) == "string" then return value end
	end
	return ""
end

local function NewActive()
	return { total = 0, cards = {}, stamp = CurStamp() }
end

local function Snapshot(s)
	local copy = {
		total = tonumber(s.total) or 0,
		stamp = s.stamp or "", cards = {},
	}
	for name, count in pairs(s.cards or {}) do copy.cards[name] = count end
	return copy
end

local function Archive(s)
	if type(s) ~= "table" or (tonumber(s.total) or 0) <= 0 then return end
	table.insert(CardCounterSet.sessions, Snapshot(s))
	while #CardCounterSet.sessions > 30 do
		table.remove(CardCounterSet.sessions, 1)
	end
end

-- skanuje caly plecak i zwraca tabelre {nazwa = suma_sztuk} dla przedmiotow
-- pasujacych do CardCounterSet.pattern (dopasowanie proste, bez wzorcow lua)
local function ScanBagCards()
	local result = {}
	local ok, used, total = pcall(GetBagCount)
	if not ok or not total then
		return result, false
	end
	local pattern = CardCounterSet.pattern or "Karta"
	for idx = 1, total do
		local ok2, invIndex, icon, name, itemCount = pcall(GetBagItemInfo, idx)
		if ok2 and name and name ~= "" then
			if string.find(name, pattern, 1, true) then
				local cnt = tonumber(itemCount) or 1
				result[name] = (result[name] or 0) + cnt
			end
		end
	end
	return result, true
end

function CardCounter.AddCard(name, count)
	if not ready or type(name) ~= "string" or name == "" then return end
	count = count or 1
	active.total = active.total + count
	active.cards[name] = (active.cards[name] or 0) + count
	CardCounterSet.total = CardCounterSet.total + count
	CardCounterSet.cards[name] = (CardCounterSet.cards[name] or 0) + count
	if CardCounterSet.chat then
		Print(string.format("%s - sesja: %d, razem: %d", name, active.cards[name], CardCounterSet.cards[name]))
	end
	-- active is CardCounterSet.current, not a temporary local-only copy.
	listDirty = true
	CardCounter.Update()
end

-- porownuje nowy stan plecaka z poprzednim i dolicza wzrosty jako zdobyte karty
local function DiffAndApply(newSnap)
	for name, cnt in pairs(newSnap) do
		local prev = (bagSnapshot and bagSnapshot[name]) or 0
		if cnt > prev then
			CardCounter.AddCard(name, cnt - prev)
		end
	end
	-- karty, ktore zniknely z plecaka (uzyte/wyrzucone) - tylko aktualizacja bazy,
	-- nie odejmujemy nic z licznika zdobytych
	bagSnapshot = newSnap
end

function CardCounter.Rescan(manual)
	local now = GetTime()
	if not manual and (now - lastScan) < SCAN_MIN_INTERVAL then
		return
	end
	lastScan = now
	local snap, ok = ScanBagCards()
	if not ok then
		if manual then
			Print("blad odczytu plecaka (GetBagCount niedostepne?).")
		end
		return
	end
	if bagSnapshot == nil then
		bagSnapshot = snap
		if manual then
			Print("zbudowano baze startowa plecaka (wzorzec: '"..(CardCounterSet.pattern or "Karta").."').")
		end
		if CardCounterSet.debug then
			local any = false
			for name, cnt in pairs(snap) do
				Print("dbg: baza -> "..name.." x"..cnt)
				any = true
			end
			if not any then Print("dbg: brak pasujacych przedmiotow w plecaku.") end
		end
		return
	end
	DiffAndApply(snap)
	if manual then
		local any = false
		for name, cnt in pairs(snap) do
			Print(name.." - w plecaku: "..cnt)
			any = true
		end
		if not any then
			Print("brak przedmiotow pasujacych do wzorca '"..(CardCounterSet.pattern or "Karta").."' w plecaku.")
		end
	end
end

function CardCounter.OnLoad(this)
	this:RegisterEvent("VARIABLES_LOADED")
end

function CardCounter.OnEvent(this, event)
	if event == "VARIABLES_LOADED" then
		if ready then return end
		for k, v in pairs(defaults) do
			if CardCounterSet[k] == nil then
				CardCounterSet[k] = type(v) == "table" and {} or v
			end
		end
		if type(CardCounterSet.sessions) ~= "table" then CardCounterSet.sessions = {} end
		if type(CardCounterSet.cards) ~= "table" then CardCounterSet.cards = {} end
		-- Aktywna sesja poprzedniego klienta byla juz w SavedVariables.
		-- Archiwizujemy ja dokladnie raz i zaczynamy nowa sesje.
		Archive(CardCounterSet.current)
		active = NewActive()
		CardCounterSet.current = active
		SaveVariablesPerCharacter("CardCounterSet")
		this:RegisterEvent("PLAYER_BAG_CHANGED")
		this:RegisterEvent("BAG_ITEM_UPDATE")
		ready = true
		CardCounter.ApplyPos()
		RestoreMinimapButton()
		CardCounterFrame:Hide()
		CardCounter.Update()
		CardCounter.Rescan(false)
		Print("v"..CardCounter.version.." zaladowany - /lk pomoc (okienko wlaczysz ikona przy minimapie)")
		return
	end
	if not ready then return end
	if event == "PLAYER_BAG_CHANGED" or event == "BAG_ITEM_UPDATE" then
		if CardCounterSet.debug then
			Print("dbg: "..event)
		end
		CardCounter.Rescan(false)
		return
	end
end

function CardCounter.OnUpdate(this)
	if not ready then return end
	local now = GetTime()
	if (now - lastPoll) >= POLL_INTERVAL then
		lastPoll = now
		CardCounter.Rescan(false)
	end
end

function CardCounter.AddManual(name, count)
	if not name or name == "" then
		Print("podaj nazwe karty, np. /lk dodaj Karta - Ayelo")
		return
	end
	CardCounter.AddCard(name, count or 1)
	Print("recznie dodano: "..name.." x"..(count or 1))
end

function CardCounter.RemoveManual(name, count)
	count = count or 1
	if not name or name == "" then
		Print("podaj nazwe karty, np. /lk usun Karta - Ayelo")
		return
	end
	if not active.cards[name] or active.cards[name] <= 0 then
		Print("brak takiej karty w sesji: "..name)
		return
	end
	active.cards[name] = math.max(0, active.cards[name] - count)
	active.total = math.max(0, active.total - count)
	CardCounterSet.cards[name] = math.max(0, (CardCounterSet.cards[name] or 0) - count)
	CardCounterSet.total = math.max(0, CardCounterSet.total - count)
	listDirty = true
	Print("recznie odjeto: "..name.." x"..count)
	CardCounter.Update()
end

function CardCounter.SetPattern(p)
	if not p or p == "" then
		Print("aktualny wzorzec: '"..(CardCounterSet.pattern or "Karta").."'")
		return
	end
	CardCounterSet.pattern = p
	bagSnapshot = nil
	CardCounter.Rescan(true)
	Print("wzorzec ustawiony na: '"..p.."' (baza plecaka przebudowana)")
end

function CardCounter.Center()
	CardCounterFrame:ClearAllAnchors()
	CardCounterFrame:SetAnchor("CENTER", "CENTER", "UIParent", 160, 0)
	CardCounterSet.hasPos = false
	CardCounterFrame:Show()
	Print("okienko wycentrowane.")
end

local function SortedCards(counts)
	local arr = {}
	for name, c in pairs(counts or {}) do
		if type(name) == "string" and type(c) == "number" and c > 0 then
			arr[#arr + 1] = { name = name, count = c }
		end
	end
	table.sort(arr, function(a, b)
		if a.count == b.count then return a.name < b.name end
		return a.count > b.count
	end)
	return arr
end

local function NameParts(name)
	-- Krotkie, osobne FontStringi omijaja limit dlugiego tekstu klienta.
	-- Nigdy nie dzielimy punktu kodowego UTF-8.
	local parts, start, chars, bytes = {}, 1, 0, 0
	local i = 1
	while i <= #name do
		local b = string.byte(name, i)
		local width = 1
		if b >= 240 and b < 248 then width = 4
		elseif b >= 224 and b < 240 then width = 3
		elseif b >= 192 and b < 224 then width = 2 end
		width = math.min(width, #name - i + 1)
		if chars >= 40 or bytes + width > 80 then
			parts[#parts + 1] = string.sub(name, start, i - 1)
			start, chars, bytes = i, 0, 0
		end
		chars, bytes = chars + 1, bytes + width
		i = i + width
	end
	if start <= #name then parts[#parts + 1] = string.sub(name, start) end
	return parts
end

local function SelectedSession()
	if not historyOpen then return active end
	return CardCounterSet.sessions[historyIndex]
end

local function BuildRows()
	displayRows, displayKinds = {}, 0
	local s = SelectedSession()
	local cards = SortedCards(s and s.cards)
	displayKinds = #cards
	for _, card in ipairs(cards) do
		local parts = NameParts(card.name)
		for i, text in ipairs(parts) do
			displayRows[#displayRows + 1] = {
				text = text, count = i == 1 and ("x"..card.count) or "",
			}
		end
	end
	if #displayRows == 0 then
		displayRows[1] = { text = historyOpen and "Brak zapisanych sesji" or "Brak zdobytych kart", count = "" }
	end
	offset = math.max(0, math.min(offset, math.max(0, #displayRows - ROW_COUNT)))
	listDirty = false
end

-- responsywne okno - w biezacej sesji okno rosnie wraz
-- z liczba wierszy; w podgladzie archiwum wraca do pelnego
-- rozmiaru (12 wierszy), zeby strzalki i nawigacja sie nie ruszaly.
local ROWS_TOP = 72
local ROW_HEIGHT = 20
local function LayoutWindow()
	if not ready then return end
	local rows
	if historyOpen then
		rows = ROW_COUNT
	else
		rows = math.max(1, math.min(#displayRows, ROW_COUNT))
	end
	local pageY = ROWS_TOP + rows * ROW_HEIGHT + 4
	CardCounterFrame_Page:ClearAllAnchors()
	CardCounterFrame_Page:SetAnchor("TOPLEFT", "TOPLEFT", "CardCounterFrame", 10, pageY)
	CardCounterFrame_HistoryBtn:ClearAllAnchors()
	CardCounterFrame_HistoryBtn:SetAnchor("TOPLEFT", "TOPLEFT", "CardCounterFrame", 10, pageY + 24)
	CardCounterFrame_Reset:ClearAllAnchors()
	CardCounterFrame_Reset:SetAnchor("TOPLEFT", "TOPLEFT", "CardCounterFrame", 120, pageY + 24)
	CardCounterFrame_ResetAll:ClearAllAnchors()
	CardCounterFrame_ResetAll:SetAnchor("TOPLEFT", "TOPLEFT", "CardCounterFrame", 10, pageY + 54)
	CardCounterFrame:SetHeight(pageY + 84)
	CardCounterFrame_Scroll:SetHeight(rows * ROW_HEIGHT - 10)
end

function CardCounter.DrawRows()
	for i = 1, ROW_COUNT do
		local row = displayRows[offset + i]
		_G["CardCounterFrame_Row"..i.."_Name"]:SetText(row and row.text or "")
		_G["CardCounterFrame_Row"..i.."_Count"]:SetText(row and row.count or "")
	end
	local maximum = math.max(0, #displayRows - ROW_COUNT)
	scrollUpdating = true
	CardCounterFrame_Scroll:SetMinMaxValues(0, maximum)
	CardCounterFrame_Scroll:SetValue(offset)
	scrollUpdating = false
	if maximum > 0 then CardCounterFrame_Scroll:Show()
	else CardCounterFrame_Scroll:Hide() end
	CardCounterFrame_Page:SetText(string.format("Wiersze %d-%d/%d | Typy: %d",
		offset + 1, math.min(offset + ROW_COUNT, #displayRows), #displayRows, displayKinds))
end

function CardCounter.OnScrollChanged(this, value)
	if scrollUpdating or not ready then return end
	offset = math.floor(tonumber(value) or this:GetValue() or 0)
	offset = math.max(0, math.min(offset, math.max(0, #displayRows - ROW_COUNT)))
	CardCounter.DrawRows()
end

function CardCounter.OnMouseWheel(delta)
	if not ready then return end
	if (tonumber(delta) or 0) > 0 then offset = offset - 3
	else offset = offset + 3 end
	offset = math.max(0, math.min(offset, math.max(0, #displayRows - ROW_COUNT)))
	CardCounter.DrawRows()
end

function CardCounter.ChangeHistory(direction)
	if not ready or not historyOpen then return end
	historyIndex = math.max(1, math.min(#CardCounterSet.sessions, historyIndex + direction))
	offset, listDirty = 0, true
	CardCounter.Update()
end

function CardCounter.Update()
	if not ready then return end
	if historyOpen then
		local s = SelectedSession()
		local n = #CardCounterSet.sessions
		CardCounterFrame_Total:SetText(s and ("Archiwum | Kart: "..s.total) or "Archiwum sesji")
		local stamp = s and s.stamp or ""
		if stamp == "" then stamp = "bez daty" end
		CardCounterFrame_Session:SetText(n > 0 and string.format("Sesja %d/%d | %s", historyIndex, n, stamp) or "Brak sesji")
		CardCounterFrame_Prev:Show()
		CardCounterFrame_Next:Show()
		if historyIndex > 1 then CardCounterFrame_Prev:Enable() else CardCounterFrame_Prev:Disable() end
		if historyIndex < n then CardCounterFrame_Next:Enable() else CardCounterFrame_Next:Disable() end
		CardCounterFrame_HistoryBtn:SetText("Wroc")
	else
		CardCounterFrame_Total:SetText(string.format("Razem: %d | Sesja: %d", CardCounterSet.total, active.total))
		CardCounterFrame_Session:SetText("Biezaca sesja")
		CardCounterFrame_Prev:Hide()
		CardCounterFrame_Next:Hide()
		CardCounterFrame_HistoryBtn:SetText("Archiwum")
	end
	-- Archiwum jest tylko do podgladu; przyciski zapisu dzialaja na biezaca.
	for _, button in ipairs({CardCounterFrame_Reset}) do
		if historyOpen then button:Disable() else button:Enable() end
	end
	if listDirty then
		BuildRows()
		CardCounter.DrawRows()
	end
	LayoutWindow()
end

function CardCounter.ToggleHistory()
	if not ready then return end
	historyOpen = not historyOpen
	if historyOpen then historyIndex = #CardCounterSet.sessions end
	offset, listDirty = 0, true
	CardCounter.Update()
end

local function NewSession()
	active = NewActive()
	CardCounterSet.current = active
	offset, listDirty = 0, true
	historyOpen = false
end

function CardCounter.ResetSession()
	if not ready then return end
	Archive(active)
	NewSession()
	CardCounter.Update()
	Print("licznik sesji zresetowany" .. (#CardCounterSet.sessions > 0 and " (poprzednia zapisana w archiwum)." or "."))
end

function CardCounter.ResetAll()
	if not ready then return end
	NewSession()
	CardCounterSet.total = 0
	CardCounterSet.cards = {}
	CardCounterSet.sessions = {}
	CardCounter.Update()
	Print("licznik calkowity i historia zresetowane.")
end

-- v1.6: pozycje przywracamy przy KAZDYM pokazaniu okienka.
function CardCounter.ApplyPos()
	if not ready or not CardCounterSet.hasPos then return end
	if CardCounterSet.posFmt ~= 3 then
		CardCounterSet.hasPos = false
		return
	end
	local mf = _G["MinimapViewFrame"]
	if not mf then return end
	CardCounterFrame:ClearAllAnchors()
	CardCounterFrame:SetAnchor(CardCounterSet.posPoint, "CENTER", "MinimapViewFrame",
		tonumber(CardCounterSet.posX) or 0, tonumber(CardCounterSet.posY) or 0)
end

function CardCounter.OnShowFrame()
	CardCounter.ApplyPos()
	CardCounter.Update()
end

function CardCounter.Toggle()
	if not ready then return end
	if CardCounterFrame:IsVisible() then
		CardCounterFrame:Hide()
	else
		CardCounter.ApplyPos()
		CardCounter.Update()
		CardCounterFrame:Show()
	end
end

-- v1.7: pozycja okienka jako offset od SRODKA minimapy (jak ikony) -
-- pixele bezwzgledne sa przez klienta skalowane przy zmianach okna,
-- kotwica do minimapy powoduje, ze okienko jest do niej zadokowane.
function CardCounter.OnDragStop(this)
	this:StopMovingOrSizing()
	local l = this.GetLeft and tonumber(this:GetLeft()) or nil
	local t = this.GetTop and tonumber(this:GetTop()) or nil
	local cx, cy, ok = MinimapCenterXY()
	if not ok or not l or not t then return end
	CardCounterSet.posPoint = "CENTER"
	CardCounterSet.posRel = "MinimapViewFrame"
	CardCounterSet.posX = math.floor(l + this:GetWidth() / 2 - cx + 0.5)
	CardCounterSet.posY = math.floor(t + this:GetHeight() / 2 - cy + 0.5)
	CardCounterSet.hasPos = true
	CardCounterSet.posFmt = 3
end

-- ikona przy minimapie
function CardCounter.MinimapClick(this, key)
	if miniDragging then
		miniDragging = false
		return
	end
	if key == "RBUTTON" then
		CardCounter.ResetSession()
	else
		CardCounter.Toggle()
	end
end

function CardCounter.MinimapDragStart(this)
	miniDragging = true
	this:StartMoving()
end

function CardCounter.MinimapDragStop(this)
	this:StopMovingOrSizing()
	-- zapis pozycji jako offset od srodka minimapy, odporny
	-- na zmiane rozdzielczosci i skali UI
	local l = this.GetLeft and tonumber(this:GetLeft()) or nil
	local t = this.GetTop and tonumber(this:GetTop()) or nil
	local cx, cy, ok = MinimapCenterXY()
	if ok and l and t then
		CardCounterSet.btnX = math.floor(l + this:GetWidth() / 2 - cx + 0.5)
		CardCounterSet.btnY = math.floor(t + this:GetHeight() / 2 - cy + 0.5)
		CardCounterSet.btnHasPos = true
		CardCounterSet.btnNorm = 2
	end
end

function CardCounter.MinimapHome()
	CardCounterSet.btnHasPos = false
	CardCounterSet.btnX = -80
	CardCounterSet.btnY = -14
	CardCounterSet.btnNorm = 2
	CardCounterMinimapButton:ClearAllAnchors()
	CardCounterMinimapButton:SetAnchor("CENTER", "CENTER", "MinimapViewFrame", -80, -14)
	CardCounterMinimapButton:Show()
	Print("ikona wrocila przy minimape.")
end

SLASH_CARDCOUNTER1 = "/lk"
SLASH_CARDCOUNTER2 = "/karty"
SLASH_CARDCOUNTER3 = "/cardcounter"
SlashCmdList["CARDCOUNTER"] = function(msg)
	if type(msg) ~= "string" then msg = "" end
	local lower = string.lower(msg)
	if lower == "reset" then
		CardCounter.ResetSession()
	elseif lower == "resetall" then
		CardCounter.ResetAll()
	elseif lower == "center" then
		CardCounter.Center()
	elseif lower == "ikona" then
		CardCounter.MinimapHome()
	elseif lower == "arch" or lower == "historia" then
		CardCounter.ToggleHistory()
		if not CardCounterFrame:IsVisible() then CardCounterFrame:Show() end
	elseif lower == "chat" then
		CardCounterSet.chat = not CardCounterSet.chat
		Print("powiadomienia o zdobyciu karty na czacie: "..(CardCounterSet.chat and "WLACZONE" or "WYLACZONE"))
	elseif lower == "debug" then
		CardCounterSet.debug = not CardCounterSet.debug
		Print("tryb debug: "..(CardCounterSet.debug and "WLACZONY" or "WYLACZONY"))
	elseif lower == "skan" then
		CardCounter.Rescan(true)
	elseif string.find(lower, "^wzorzec") then
		local p = string.match(msg, "^%S+%s*(.-)%s*$")
		CardCounter.SetPattern(p)
	elseif string.find(lower, "^dodaj") then
		local name = string.match(msg, "^%S+%s*(.-)%s*$")
		CardCounter.AddManual(name, 1)
	elseif string.find(lower, "^usun") then
		local name = string.match(msg, "^%S+%s*(.-)%s*$")
		CardCounter.RemoveManual(name, 1)
	elseif lower == "pomoc" or lower == "help" then
		Print("/lk - pokaz/ukryj okienko")
		Print("/lk reset - zapisz sesje w archiwum i zacznij nowa")
		Print("/lk resetall - reset wszystkich licznikow i historii")
		Print("/lk arch - archiwum poprzednich sesji (strzalki, suwak)")
		Print("/lk skan - recznie przeskanuj plecak i pokaz co pasuje do wzorca")
		Print("/lk wzorzec <tekst> - zmien dopasowywany fragment nazwy (domyslnie: Karta)")
		Print("/lk dodaj <nazwa> - recznie dodaj +1 dla podanej karty")
		Print("/lk usun <nazwa> - recznie odejmij -1 dla podanej karty (korekta)")
		Print("/lk center - przenies okienko na srodek ekranu")
		Print("/lk ikona - przywroc ikone obok minimapy")
		Print("/lk chat - wl./wyl. powiadomienia o zdobyciu karty na czacie")
		Print("/lk debug - wl./wyl. podglad eventow i skanow (do diagnostyki)")
	else
		CardCounter.Toggle()
	end
end
