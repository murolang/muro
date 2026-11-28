package engine

import (
	"errors"
	"fmt"
	"sort"
)

// Phase is the phase of one live or retained row.
type Phase uint8

const (
	// PhaseOpen is Agda opened. The row can be resolved.
	PhaseOpen Phase = iota
	// PhaseHeld is waiting on another row of the same key.
	PhaseHeld
	// PhaseResolved is kept only when the family may revert.
	PhaseResolved
)

// String returns open, held, or resolved.
func (p Phase) String() string {
	switch p {
	case PhaseOpen:
		return "open"
	case PhaseHeld:
		return "held"
	case PhaseResolved:
		return "resolved"
	default:
		return "phase"
	}
}

// Outcome selects resolve or rerun for Finish.
type Outcome uint8

const (
	// OutcomeResolve drops an open row and releases what that opens.
	OutcomeResolve Outcome = iota
	// OutcomeRerun checks that the row is open and leaves it.
	OutcomeRerun
)

// String returns resolve or rerun.
func (o Outcome) String() string {
	switch o {
	case OutcomeResolve:
		return "resolve"
	case OutcomeRerun:
		return "rerun"
	default:
		return "outcome"
	}
}

// Released is one row that moved from held to open.
type Released struct {
	ID   int
	Key  string
	Kind string
}

// Row is one dispatcher row. View returns rows sorted by key, index, then id.
type Row struct {
	Key   string
	Index int
	ID    int
	Kind  string
	Phase Phase
}

// ErrFamily is the parent of every dispatcher sentinel.
var ErrFamily = errors.New("muro: family")

// Dispatcher sentinels. errors.Is matches the sentinel and ErrFamily.
var (
	ErrDuplicate  = muroSentinel(ErrFamily, "muro: duplicate")
	ErrDeparted   = muroSentinel(ErrFamily, "muro: departed")
	ErrUnknown    = muroSentinel(ErrFamily, "muro: unknown")
	ErrHeld       = muroSentinel(ErrFamily, "muro: held")
	ErrOpened     = muroSentinel(ErrFamily, "muro: opened")
	ErrResolved   = muroSentinel(ErrFamily, "muro: resolved")
	ErrWithdrawn  = muroSentinel(ErrFamily, "muro: withdrawn")
	ErrHeldBy     = muroSentinel(ErrFamily, "muro: held by")
	ErrLive       = muroSentinel(ErrFamily, "muro: live")
	ErrKind       = muroSentinel(ErrFamily, "muro: kind")
	ErrBadState   = muroSentinel(ErrFamily, "muro: bad state")
	ErrIndex      = muroSentinel(ErrFamily, "muro: index")
	ErrUnmarked   = muroSentinel(ErrFamily, "muro: unmarked")
	ErrUnfinished = muroSentinel(ErrFamily, "muro: unfinished")
)

type muroCode struct {
	text   string
	parent error
}

func (e *muroCode) Error() string { return e.text }
func (e *muroCode) Unwrap() error { return e.parent }

func muroSentinel(parent error, text string) error {
	return &muroCode{text: text, parent: parent}
}

// FamilyError is a refused dispatcher step. Unwrap yields the sentinel.
type FamilyError struct {
	Code  error
	Key   string
	Index int
	ID    int
	Kind  string
	IDs   []int
}

// Error describes the refused step.
func (e *FamilyError) Error() string {
	if e == nil || e.Code == nil {
		return "muro: family"
	}
	switch {
	case errors.Is(e.Code, ErrDuplicate):
		return fmt.Sprintf("muro: duplicate key %s index %d", e.Key, e.Index)
	case errors.Is(e.Code, ErrDeparted):
		return fmt.Sprintf("muro: departed key %s index %d", e.Key, e.Index)
	case errors.Is(e.Code, ErrIndex):
		return fmt.Sprintf("muro: index %d", e.Index)
	case errors.Is(e.Code, ErrKind):
		return fmt.Sprintf("muro: kind %s", e.Kind)
	case errors.Is(e.Code, ErrHeldBy):
		return fmt.Sprintf("muro: held by %v", e.IDs)
	case errors.Is(e.Code, ErrLive):
		return fmt.Sprintf("muro: live key %s", e.Key)
	case e.ID >= 0:
		return fmt.Sprintf("%s id %d", e.Code.Error(), e.ID)
	default:
		return e.Code.Error()
	}
}

// Unwrap returns the sentinel.
func (e *FamilyError) Unwrap() error {
	if e == nil {
		return nil
	}
	return e.Code
}

func famErr(code error) *FamilyError {
	return &FamilyError{Code: code, Index: -1, ID: -1}
}

func famErrAt(code error, key string, index int) *FamilyError {
	return &FamilyError{Code: code, Key: key, Index: index, ID: -1}
}

func famErrID(code error, id int) *FamilyError {
	return &FamilyError{Code: code, Index: -1, ID: id}
}

func famErrIDs(code error, ids []int) *FamilyError {
	return &FamilyError{Code: code, Index: -1, ID: -1, IDs: ids}
}

func famErrKind(kind string) *FamilyError {
	return &FamilyError{Code: ErrKind, Index: -1, ID: -1, Kind: kind}
}

const (
	holdNever uint8 = iota
	holdEarlier
	holdAny
	holdNamed
	holdMissing uint8 = 255
)

type holdRule struct {
	mode  uint8
	while []uint8
	until []uint8
}

type famRow struct {
	key      string
	index    int
	id       int
	born     int
	openedAt int
	kind     uint8
	phase    Phase
}

type famDep struct {
	prefix int
	gaps   map[int]struct{}
}

type famLeft struct {
	key   string
	index int
}

type famState struct {
	ready     bool
	next      int
	tick      int
	floor     int
	rows      []famRow
	departed  map[string]famDep
	kinds     map[string]map[uint8]struct{}
	withdrawn map[int]famLeft
}

type famRel struct {
	id    int
	key   string
	kind  uint8
	index int
}

func muroFamFresh(rows []famRow, key string, index int) bool {
	for _, row := range rows {
		if row.key == key && row.index == index {
			return false
		}
	}
	return true
}

func muroFamRecord(st famState, key string) (int, map[int]struct{}) {
	if st.departed == nil {
		return -1, nil
	}
	rec, ok := st.departed[key]
	if !ok {
		return -1, nil
	}
	return rec.prefix, rec.gaps
}

func muroFamGone(st famState, key string, index int) bool {
	prefix, gaps := muroFamRecord(st, key)
	if index <= st.floor || index <= prefix {
		return true
	}
	_, hit := gaps[index]
	return hit
}

func muroFamHold(rules []holdRule, kind uint8) (holdRule, bool) {
	if int(kind) >= len(rules) {
		return holdRule{}, false
	}
	rule := rules[kind]
	if rule.mode == holdMissing {
		return holdRule{}, false
	}
	return rule, true
}

func muroFamBlocked(rows []famRow, key string, index int) bool {
	for _, row := range rows {
		if row.key == key && row.index < index && row.phase != PhaseResolved {
			return true
		}
	}
	return false
}

func muroFamAnyBlocked(rows []famRow, key string, index int) bool {
	for _, row := range rows {
		if row.key == key && row.index != index && row.phase == PhaseOpen {
			return true
		}
	}
	return false
}

func muroFamKindLive(rows []famRow, key string, kind uint8) bool {
	for _, row := range rows {
		if row.key == key && row.kind == kind && (row.phase == PhaseOpen || row.phase == PhaseHeld) {
			return true
		}
	}
	return false
}

func muroFamFacts(st famState, key string) map[uint8]struct{} {
	if st.kinds == nil {
		return nil
	}
	return st.kinds[key]
}

func muroFamNamedBlocked(rule holdRule, rows []famRow, key string, facts map[uint8]struct{}) bool {
	for _, kind := range rule.while {
		if muroFamKindLive(rows, key, kind) {
			return true
		}
	}
	for _, kind := range rule.until {
		if _, ok := facts[kind]; !ok {
			return true
		}
	}
	return false
}

func muroFamDecide(rows []famRow, key string, index int, kind uint8, rules []holdRule, facts map[uint8]struct{}) Phase {
	rule, _ := muroFamHold(rules, kind)
	switch rule.mode {
	case holdEarlier:
		if muroFamBlocked(rows, key, index) {
			return PhaseHeld
		}
		return PhaseOpen
	case holdAny:
		if muroFamAnyBlocked(rows, key, index) {
			return PhaseHeld
		}
		return PhaseOpen
	case holdNamed:
		if muroFamNamedBlocked(rule, rows, key, facts) {
			return PhaseHeld
		}
		return PhaseOpen
	default:
		return PhaseOpen
	}
}

func muroFamArrive(st famState, key string, kind uint8, index int, rules []holdRule, names []string) (famState, Phase, int, *FamilyError) {
	if index < 0 {
		return st, 0, -1, &FamilyError{Code: ErrIndex, Index: index, ID: -1}
	}
	if _, ok := muroFamHold(rules, kind); !ok {
		label := "kind"
		if int(kind) < len(names) {
			label = names[kind]
		}
		return st, 0, -1, famErrKind(label)
	}
	if !muroFamFresh(st.rows, key, index) {
		return st, 0, -1, famErrAt(ErrDuplicate, key, index)
	}
	if muroFamGone(st, key, index) {
		return st, 0, -1, famErrAt(ErrDeparted, key, index)
	}
	phase := muroFamDecide(st.rows, key, index, kind, rules, muroFamFacts(st, key))
	id := st.next
	row := famRow{
		key:      key,
		index:    index,
		id:       id,
		born:     st.tick,
		openedAt: st.tick,
		kind:     kind,
		phase:    phase,
	}
	rows := make([]famRow, 0, len(st.rows)+1)
	rows = append(rows, row)
	rows = append(rows, st.rows...)
	st.next = id + 1
	st.tick = st.tick + 1
	st.rows = rows
	return st, phase, id, nil
}

func muroFamFind(rows []famRow, id int) (famRow, bool) {
	for _, row := range rows {
		if row.id == id {
			return row, true
		}
	}
	return famRow{}, false
}

func muroFamRemove(rows []famRow, id int) []famRow {
	out := make([]famRow, 0, len(rows))
	for _, row := range rows {
		if row.id != id {
			out = append(out, row)
		}
	}
	return out
}

func muroFamSetPhase(rows []famRow, id int, phase Phase) []famRow {
	out := make([]famRow, len(rows))
	copy(out, rows)
	for i := range out {
		if out[i].id == id {
			out[i].phase = phase
		}
	}
	return out
}

func muroFamIsAny(rules []holdRule, kind uint8) bool {
	rule, ok := muroFamHold(rules, kind)
	return ok && rule.mode == holdAny
}

func muroFamIsEarlier(rules []holdRule, kind uint8) bool {
	rule, ok := muroFamHold(rules, kind)
	return ok && rule.mode == holdEarlier
}

func muroFamIsNamed(rules []holdRule, kind uint8) bool {
	rule, ok := muroFamHold(rules, kind)
	return ok && rule.mode == holdNamed
}

func muroFamCandidate(key string, rows []famRow, row famRow, rules []holdRule, facts map[uint8]struct{}) bool {
	if row.key != key || row.phase != PhaseHeld {
		return false
	}
	switch {
	case muroFamIsEarlier(rules, row.kind):
		return !muroFamBlocked(rows, row.key, row.index)
	case muroFamIsAny(rules, row.kind):
		return !muroFamAnyBlocked(rows, row.key, row.index)
	case muroFamIsNamed(rules, row.kind):
		rule, _ := muroFamHold(rules, row.kind)
		return !muroFamNamedBlocked(rule, rows, key, facts)
	default:
		return false
	}
}

func muroFamMin(rows []famRow) famRow {
	best := rows[0]
	for _, row := range rows[1:] {
		if row.index < best.index || (row.index == best.index && row.id < best.id) {
			best = row
		}
	}
	return best
}

func muroFamOneOfAny(cands []famRow, rules []holdRule) []famRow {
	var anys, rest []famRow
	for _, row := range cands {
		if muroFamIsAny(rules, row.kind) {
			anys = append(anys, row)
		} else {
			rest = append(rest, row)
		}
	}
	if len(anys) == 0 {
		return rest
	}
	if len(rest) == 0 {
		return []famRow{muroFamMin(anys)}
	}
	return rest
}

func muroFamOpenAll(key string, rows []famRow, tick int, rules []holdRule, facts map[uint8]struct{}) ([]famRow, []famRel) {
	var cands []famRow
	for _, row := range rows {
		if muroFamCandidate(key, rows, row, rules, facts) {
			cands = append(cands, row)
		}
	}
	chosen := muroFamOneOfAny(cands, rules)
	ids := map[int]struct{}{}
	for _, row := range chosen {
		ids[row.id] = struct{}{}
	}
	out := make([]famRow, len(rows))
	copy(out, rows)
	for i := range out {
		if _, ok := ids[out[i].id]; ok {
			out[i].openedAt = tick
			out[i].phase = PhaseOpen
		}
	}
	sort.Slice(chosen, func(i, j int) bool {
		if chosen[i].index != chosen[j].index {
			return chosen[i].index < chosen[j].index
		}
		return chosen[i].id < chosen[j].id
	})
	rel := make([]famRel, len(chosen))
	for i, row := range chosen {
		rel[i] = famRel{id: row.id, key: row.key, kind: row.kind, index: row.index}
	}
	return out, rel
}

func muroFamRecords(rules []holdRule, kind uint8) bool {
	for _, rule := range rules {
		for _, until := range rule.until {
			if until == kind {
				return true
			}
		}
	}
	return false
}

func muroFamNoteResolved(st famState, key string, kind uint8, rules []holdRule) famState {
	if !muroFamRecords(rules, kind) {
		return st
	}
	kinds := muroFamCopyKinds(st.kinds)
	inner := map[uint8]struct{}{}
	if kinds[key] != nil {
		for k, v := range kinds[key] {
			inner[k] = v
		}
	}
	inner[kind] = struct{}{}
	kinds[key] = inner
	st.kinds = kinds
	return st
}

func muroFamCopyKinds(kinds map[string]map[uint8]struct{}) map[string]map[uint8]struct{} {
	out := map[string]map[uint8]struct{}{}
	for key, inner := range kinds {
		cp := map[uint8]struct{}{}
		for k, v := range inner {
			cp[k] = v
		}
		out[key] = cp
	}
	return out
}

func muroFamCopyDeps(deps map[string]famDep) map[string]famDep {
	out := map[string]famDep{}
	for key, rec := range deps {
		out[key] = famDep{prefix: rec.prefix, gaps: muroFamCopyGaps(rec.gaps)}
	}
	return out
}

func muroFamCopyGaps(gaps map[int]struct{}) map[int]struct{} {
	out := map[int]struct{}{}
	for ix := range gaps {
		out[ix] = struct{}{}
	}
	return out
}

func muroFamCopyWithdrawn(in map[int]famLeft) map[int]famLeft {
	out := map[int]famLeft{}
	for id, left := range in {
		out[id] = left
	}
	return out
}

func muroFamFold(prefix int, gaps map[int]struct{}) (int, map[int]struct{}) {
	for {
		next := prefix + 1
		if _, ok := gaps[next]; !ok {
			return prefix, gaps
		}
		delete(gaps, next)
		prefix = next
	}
}

func muroFamPack(prefix, floor int, gaps map[int]struct{}) (bool, int, map[int]struct{}) {
	if prefix < floor {
		prefix = floor
	}
	kept := map[int]struct{}{}
	for ix := range gaps {
		if ix > prefix {
			kept[ix] = struct{}{}
		}
	}
	prefix, kept = muroFamFold(prefix, kept)
	if prefix <= floor && len(kept) == 0 {
		return false, 0, nil
	}
	return true, prefix, kept
}

func muroFamNoteDeparted(st famState, key string, index int) famState {
	if index <= st.floor {
		return st
	}
	prefix, gaps := muroFamRecord(st, key)
	deps := muroFamCopyDeps(st.departed)
	keep, packedP, packedG := muroFamPack(prefix, st.floor, gaps)
	if !keep {
		p, g := muroFamFold(st.floor, map[int]struct{}{index: {}})
		deps[key] = famDep{prefix: p, gaps: g}
		st.departed = deps
		return st
	}
	if index <= packedP {
		deps[key] = famDep{prefix: packedP, gaps: packedG}
		st.departed = deps
		return st
	}
	if _, ok := packedG[index]; ok {
		deps[key] = famDep{prefix: packedP, gaps: packedG}
		st.departed = deps
		return st
	}
	packedG[index] = struct{}{}
	p, g := muroFamFold(packedP, packedG)
	deps[key] = famDep{prefix: p, gaps: g}
	st.departed = deps
	return st
}

func muroFamNoteWithdrawn(st famState, row famRow) famState {
	out := muroFamCopyWithdrawn(st.withdrawn)
	out[row.id] = famLeft{key: row.key, index: row.index}
	st.withdrawn = out
	return st
}

func muroFamRelease(st famState, id int, rules []holdRule, record, revert bool) (famState, []famRel, *FamilyError) {
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		return st, nil, famErrID(ErrUnknown, id)
	}
	depart := true
	if record && revert {
		st.rows = muroFamSetPhase(st.rows, id, PhaseResolved)
		depart = false
	} else {
		st.rows = muroFamRemove(st.rows, id)
	}
	if record {
		st = muroFamNoteResolved(st, row.key, row.kind, rules)
	}
	facts := muroFamFacts(st, row.key)
	var rel []famRel
	st.rows, rel = muroFamOpenAll(row.key, st.rows, st.tick, rules, facts)
	st.tick = st.tick + 1
	if depart {
		st = muroFamNoteDeparted(st, row.key, row.index)
		if !record && revert {
			st = muroFamNoteWithdrawn(st, row)
		}
	}
	return st, rel, nil
}

func muroFamResolve(st famState, id int, rules []holdRule, revert bool) (famState, []famRel, *FamilyError) {
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		return st, nil, famErrID(ErrUnknown, id)
	}
	switch row.phase {
	case PhaseHeld:
		return st, nil, famErrID(ErrHeld, id)
	case PhaseResolved:
		return st, nil, famErrID(ErrResolved, id)
	case PhaseOpen:
		return muroFamRelease(st, id, rules, true, revert)
	default:
		return st, nil, famErr(ErrBadState)
	}
}

func muroFamLeft(st famState, id int) bool {
	return id >= 0 && id < st.next
}

func muroFamWithdraw(st famState, id int, rules []holdRule, revert bool) (famState, []famRel, *FamilyError) {
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		if muroFamLeft(st, id) {
			return st, nil, famErrID(ErrResolved, id)
		}
		return st, nil, famErrID(ErrUnknown, id)
	}
	switch row.phase {
	case PhaseOpen:
		return st, nil, famErrID(ErrOpened, id)
	case PhaseResolved:
		return st, nil, famErrID(ErrResolved, id)
	case PhaseHeld:
		return muroFamRelease(st, id, rules, false, revert)
	default:
		return st, nil, famErr(ErrBadState)
	}
}

func muroFamLivePairs(rows []famRow, want uint8) [][2]int {
	var hits [][2]int
	for _, row := range rows {
		if row.kind == want && (row.phase == PhaseOpen || row.phase == PhaseHeld) {
			hits = append(hits, [2]int{row.index, row.id})
		}
	}
	sort.Slice(hits, func(i, j int) bool {
		if hits[i][0] != hits[j][0] {
			return hits[i][0] < hits[j][0]
		}
		return hits[i][1] < hits[j][1]
	})
	return hits
}

func muroFamUntilFamily(rules []holdRule) bool {
	for _, rule := range rules {
		if len(rule.until) > 0 {
			return true
		}
	}
	return false
}

func muroFamClassic(rows []famRow, key string, index int, mode uint8) ([]uint8, []int, bool) {
	var hits []famRow
	for _, row := range rows {
		if row.key != key {
			continue
		}
		switch mode {
		case holdEarlier:
			if row.index < index && (row.phase == PhaseOpen || row.phase == PhaseHeld) {
				hits = append(hits, row)
			}
		case holdAny:
			if row.index != index && row.phase == PhaseOpen {
				hits = append(hits, row)
			}
		}
	}
	sort.Slice(hits, func(i, j int) bool {
		if hits[i].index != hits[j].index {
			return hits[i].index < hits[j].index
		}
		return hits[i].id < hits[j].id
	})
	var kinds []uint8
	var ids []int
	seen := map[uint8]struct{}{}
	for _, row := range hits {
		if _, ok := seen[row.kind]; !ok {
			seen[row.kind] = struct{}{}
			kinds = append(kinds, row.kind)
		}
		ids = append(ids, row.id)
	}
	return kinds, ids, true
}

func muroFamNamedHits(st famState, rows []famRow, row famRow, rule holdRule, rules []holdRule) ([]uint8, []int, bool) {
	var keyRows []famRow
	for _, other := range rows {
		if other.key == row.key {
			keyRows = append(keyRows, other)
		}
	}
	var kinds []uint8
	var pairs [][2]int
	for _, kind := range rule.while {
		hits := muroFamLivePairs(keyRows, kind)
		if len(hits) > 0 {
			kinds = append(kinds, kind)
			pairs = append(pairs, hits...)
		}
	}
	if muroFamUntilFamily(rules) {
		facts := muroFamFacts(st, row.key)
		listed := map[uint8]struct{}{}
		for _, kind := range kinds {
			listed[kind] = struct{}{}
		}
		for _, kind := range rule.until {
			if _, fact := facts[kind]; fact {
				continue
			}
			if _, already := listed[kind]; already {
				continue
			}
			kinds = append(kinds, kind)
			listed[kind] = struct{}{}
			pairs = append(pairs, muroFamLivePairs(keyRows, kind)...)
		}
	}
	sort.Slice(pairs, func(i, j int) bool {
		if pairs[i][0] != pairs[j][0] {
			return pairs[i][0] < pairs[j][0]
		}
		return pairs[i][1] < pairs[j][1]
	})
	var ids []int
	seen := map[int]struct{}{}
	for _, pair := range pairs {
		if _, ok := seen[pair[1]]; ok {
			continue
		}
		seen[pair[1]] = struct{}{}
		ids = append(ids, pair[1])
	}
	return kinds, ids, true
}

func muroFamWaiting(st famState, id int, rules []holdRule, names []string) ([]string, []int, *FamilyError) {
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		return nil, nil, famErrID(ErrUnknown, id)
	}
	switch row.phase {
	case PhaseOpen:
		return nil, nil, famErrID(ErrOpened, id)
	case PhaseResolved:
		return nil, nil, famErrID(ErrUnknown, id)
	case PhaseHeld:
		rule, good := muroFamHold(rules, row.kind)
		if !good {
			return nil, nil, famErr(ErrBadState)
		}
		var kindIDs []uint8
		var ids []int
		switch rule.mode {
		case holdEarlier:
			kindIDs, ids, _ = muroFamClassic(st.rows, row.key, row.index, holdEarlier)
		case holdAny:
			kindIDs, ids, _ = muroFamClassic(st.rows, row.key, row.index, holdAny)
		case holdNamed:
			kindIDs, ids, _ = muroFamNamedHits(st, st.rows, row, rule, rules)
		default:
			return nil, nil, famErr(ErrBadState)
		}
		if len(kindIDs) == 0 && len(ids) == 0 {
			return nil, nil, famErr(ErrBadState)
		}
		labels := make([]string, len(kindIDs))
		for i, kind := range kindIDs {
			if int(kind) < len(names) {
				labels[i] = names[kind]
			}
		}
		return labels, ids, nil
	default:
		return nil, nil, famErr(ErrBadState)
	}
}

func muroFamSkip(st famState, key string, index int) (famState, *FamilyError) {
	if index < 0 {
		return st, &FamilyError{Code: ErrIndex, Index: index, ID: -1}
	}
	if !muroFamFresh(st.rows, key, index) {
		return st, famErrAt(ErrDuplicate, key, index)
	}
	if index <= st.floor {
		return st, nil
	}
	return muroFamNoteDeparted(st, key, index), nil
}

func muroFamLiveKey(rows []famRow, key string) bool {
	for _, row := range rows {
		if row.key == key && row.phase != PhaseResolved {
			return true
		}
	}
	return false
}

func muroFamDropKey(st famState, key string) (famState, *FamilyError) {
	if muroFamLiveKey(st.rows, key) {
		return st, &FamilyError{Code: ErrLive, Key: key, Index: -1, ID: -1}
	}
	if st.departed != nil {
		deps := muroFamCopyDeps(st.departed)
		delete(deps, key)
		st.departed = deps
	}
	if st.kinds != nil {
		kinds := muroFamCopyKinds(st.kinds)
		delete(kinds, key)
		st.kinds = kinds
	}
	var keep []famRow
	for _, row := range st.rows {
		if row.key == key && row.phase == PhaseResolved {
			continue
		}
		keep = append(keep, row)
	}
	st.rows = keep
	if st.withdrawn != nil {
		out := map[int]famLeft{}
		for id, left := range st.withdrawn {
			if left.key != key {
				out[id] = left
			}
		}
		st.withdrawn = out
	}
	return st, nil
}

func muroFamDropFact(st famState, key string, kind uint8) famState {
	if st.kinds == nil {
		return st
	}
	for _, row := range st.rows {
		if row.key == key && row.kind == kind && row.phase == PhaseResolved {
			return st
		}
	}
	kinds := muroFamCopyKinds(st.kinds)
	inner := kinds[key]
	if inner == nil {
		delete(kinds, key)
		st.kinds = kinds
		return st
	}
	delete(inner, kind)
	if len(inner) == 0 {
		delete(kinds, key)
	} else {
		kinds[key] = inner
	}
	st.kinds = kinds
	return st
}

func muroFamSkipBelow(st famState, index int) (famState, *FamilyError) {
	if index < 0 {
		return st, &FamilyError{Code: ErrIndex, Index: index, ID: -1}
	}
	if index <= st.floor {
		return st, nil
	}
	deps := map[string]famDep{}
	keys := make([]string, 0, len(st.departed))
	for key := range st.departed {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	for _, key := range keys {
		rec := st.departed[key]
		keep, prefix, gaps := muroFamPack(rec.prefix, index, rec.gaps)
		if keep {
			deps[key] = famDep{prefix: prefix, gaps: gaps}
		}
	}
	st.departed = deps
	st.floor = index
	if st.withdrawn != nil {
		out := map[int]famLeft{}
		for id, left := range st.withdrawn {
			if left.index > index {
				out[id] = left
			}
		}
		st.withdrawn = out
	}
	var drop []famRow
	var keepRows []famRow
	for _, row := range st.rows {
		if row.phase == PhaseResolved && row.index <= index {
			drop = append(drop, row)
			continue
		}
		keepRows = append(keepRows, row)
	}
	if len(drop) > 0 {
		st.rows = keepRows
		for _, row := range drop {
			st = muroFamDropFact(st, row.key, row.kind)
		}
	}
	return st, nil
}

func muroFamBehind(target, other famRow, rules []holdRule) bool {
	if other.key != target.key || other.id == target.id {
		return false
	}
	if other.phase != PhaseOpen && other.phase != PhaseResolved {
		return false
	}
	rule, ok := muroFamHold(rules, other.kind)
	if !ok {
		return false
	}
	switch rule.mode {
	case holdNever:
		return false
	case holdEarlier, holdAny:
		return other.index > target.index
	case holdNamed:
		for _, kind := range rule.while {
			if kind == target.kind {
				return true
			}
		}
		for _, kind := range rule.until {
			if kind == target.kind {
				return true
			}
		}
		return false
	default:
		return false
	}
}

func muroFamBlockers(rows []famRow, target famRow, rules []holdRule) []int {
	type hit struct {
		index int
		id    int
	}
	var hits []hit
	for _, other := range rows {
		if muroFamBehind(target, other, rules) {
			hits = append(hits, hit{index: other.index, id: other.id})
		}
	}
	sort.Slice(hits, func(i, j int) bool {
		if hits[i].index != hits[j].index {
			return hits[i].index < hits[j].index
		}
		return hits[i].id < hits[j].id
	})
	ids := make([]int, len(hits))
	for i, h := range hits {
		ids[i] = h.id
	}
	return ids
}

func muroFamWithdrawn(st famState, id int) bool {
	if st.withdrawn == nil {
		return false
	}
	_, ok := st.withdrawn[id]
	return ok
}

func muroFamRevert(st famState, id int, rules []holdRule, marked bool) (famState, *FamilyError) {
	if !marked {
		return st, famErr(ErrUnmarked)
	}
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		if !muroFamLeft(st, id) {
			return st, famErrID(ErrUnknown, id)
		}
		if muroFamWithdrawn(st, id) {
			return st, famErrID(ErrWithdrawn, id)
		}
		return st, famErrID(ErrUnknown, id)
	}
	switch row.phase {
	case PhaseOpen:
		return st, famErrID(ErrOpened, id)
	case PhaseHeld:
		return st, famErrID(ErrHeld, id)
	case PhaseResolved:
		ids := muroFamBlockers(st.rows, row, rules)
		if len(ids) > 0 {
			return st, famErrIDs(ErrHeldBy, ids)
		}
		st.rows = muroFamSetPhase(st.rows, row.id, PhaseOpen)
		st.tick = st.tick + 1
		st = muroFamDropFact(st, row.key, row.kind)
		return st, nil
	default:
		return st, famErr(ErrBadState)
	}
}

func muroFamRerun(st famState, id int) (famState, *FamilyError) {
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		return st, famErrID(ErrUnknown, id)
	}
	switch row.phase {
	case PhaseHeld:
		return st, famErrID(ErrHeld, id)
	case PhaseResolved:
		return st, famErrID(ErrResolved, id)
	case PhaseOpen:
		return st, nil
	default:
		return st, famErr(ErrBadState)
	}
}

func muroFamLive(st famState, id int) (Phase, string, uint8, *FamilyError) {
	row, ok := muroFamFind(st.rows, id)
	if !ok {
		return 0, "", 0, famErrID(ErrUnknown, id)
	}
	switch row.phase {
	case PhaseResolved:
		return 0, "", 0, famErrID(ErrResolved, id)
	case PhaseOpen, PhaseHeld:
		return row.phase, row.key, row.kind, nil
	default:
		return 0, "", 0, famErr(ErrBadState)
	}
}

func muroFamView(st famState, names []string) []Row {
	out := make([]Row, len(st.rows))
	for i, row := range st.rows {
		kind := ""
		if int(row.kind) < len(names) {
			kind = names[row.kind]
		}
		out[i] = Row{Key: row.key, Index: row.index, ID: row.id, Kind: kind, Phase: row.phase}
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Key != out[j].Key {
			return out[i].Key < out[j].Key
		}
		if out[i].Index != out[j].Index {
			return out[i].Index < out[j].Index
		}
		return out[i].ID < out[j].ID
	})
	return out
}

func muroFamGaps(gaps map[int]struct{}) []int {
	out := make([]int, 0, len(gaps))
	for ix := range gaps {
		out = append(out, ix)
	}
	sort.Ints(out)
	return out
}

func muroFamReleased(rel []famRel, names []string) []Released {
	out := make([]Released, len(rel))
	for i, row := range rel {
		kind := ""
		if int(row.kind) < len(names) {
			kind = names[row.kind]
		}
		out[i] = Released{ID: row.id, Key: row.key, Kind: kind}
	}
	return out
}

func muroFamReady(st famState) *FamilyError {
	if !st.ready || st.floor < -1 {
		return famErr(ErrBadState)
	}
	return nil
}
