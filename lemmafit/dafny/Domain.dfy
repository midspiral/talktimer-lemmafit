// Verified domain logic for Talk Timer
// Models lap timing, section labeling, and manual take selection
// See SPEC.md for requirements

include "Replay.dfy"

module TalkTimer refines Domain {
  // A recorded lap marker with its own stored duration
  datatype Lap = Lap(
    timestamp: int,     // ms from session start when lap was recorded
    duration: int,      // duration of this take (stored, not computed)
    section: string,    // section label (empty string = unlabeled)
    selected: bool,     // true if this take is selected for total
    expectedDuration: int,  // expected duration from practice template (-1 = none)
    tags: seq<string>   // tags associated with this lap (unique strings)
  )

  // Template entry for practice mode
  datatype TemplateEntry = TemplateEntry(section: string, expectedDuration: int, tags: seq<string>)

  // The timer state
  datatype Model = Model(
    currentTime: int,   // current elapsed ms
    lastLapTime: int,   // timestamp of previous lap (for computing next duration)
    laps: seq<Lap>,     // recorded lap markers
    template: seq<TemplateEntry>,  // practice mode template queue (remaining)
    originalTemplate: seq<TemplateEntry>,  // original template for reset
    activeSection: int  // -1 = no active section (use sequential), >= 0 = index into originalTemplate
  )

  // User actions
  datatype Action =
    | SetTime(ms: int)                      // advance timer to given time
    | CreateLap                             // record lap at current time
    | LabelLap(idx: int, name: string)      // assign section name to lap
    | SelectLap(idx: int)                   // toggle selection of a lap
    | DeleteLap(idx: int)                   // remove a lap
    | AdjustDuration(idx: int, duration: int)  // manually adjust lap duration
    | MoveUp(idx: int)                      // move lap up (swap with previous)
    | MoveDown(idx: int)                    // move lap down (swap with next)
    | AddTag(idx: int, tag: string)         // add tag to lap (if not present)
    | RemoveTag(idx: int, tag: string)      // remove tag from lap (if present)
    | SetTemplate(labels: seq<TemplateEntry>)  // set practice template queue
    | ConsumeTemplate                       // label last lap from template, select it
    | SetActiveSection(idx: int)            // set active section for jump-to practice (-1 to clear)
    | ApplyActiveSection                    // label last lap from active section (doesn't consume queue)
    | AdvanceTemplateAfter(idx: int)        // advance template queue to after idx in originalTemplate
    | ImportLaps(laps: seq<Lap>)            // import multiple laps at once
    | Reset                                 // restore original template as laps, or clear all if not in practice mode

  //----------------------------------------------------------------------
  // Helpers
  //----------------------------------------------------------------------

  // Check if a tag exists in a sequence
  predicate TagIn(tag: string, tags: seq<string>) {
    tag in tags
  }

  // Add a tag to the sequence if not already present
  function AddTagToSeq(tags: seq<string>, tag: string): seq<string>
  {
    if tag in tags then tags else tags + [tag]
  }

  // Remove a tag from the sequence (filter out all occurrences)
  function RemoveTagFromSeq(tags: seq<string>, tag: string): seq<string>
    decreases |tags|
  {
    if |tags| == 0 then []
    else if tags[0] == tag then RemoveTagFromSeq(tags[1..], tag)
    else [tags[0]] + RemoveTagFromSeq(tags[1..], tag)
  }

  // Lemma: AddTagToSeq ensures tag is in result
  lemma AddTagEnsuresPresence(tags: seq<string>, tag: string)
    ensures tag in AddTagToSeq(tags, tag)
  {}

  // Lemma: RemoveTagFromSeq ensures tag is not in result
  lemma RemoveTagEnsuresAbsence(tags: seq<string>, tag: string)
    ensures tag !in RemoveTagFromSeq(tags, tag)
  {
    if |tags| == 0 {
    } else if tags[0] == tag {
      RemoveTagEnsuresAbsence(tags[1..], tag);
    } else {
      RemoveTagEnsuresAbsence(tags[1..], tag);
    }
  }

  // Lemma: RemoveTagFromSeq preserves other tags
  lemma RemoveTagPreservesOthers(tags: seq<string>, tag: string, other: string)
    requires other != tag
    requires other in tags
    ensures other in RemoveTagFromSeq(tags, tag)
  {
    if |tags| == 0 {
    } else if tags[0] == tag {
      assert other in tags[1..];
      RemoveTagPreservesOthers(tags[1..], tag, other);
    } else if tags[0] == other {
      // other is at position 0, preserved
    } else {
      RemoveTagPreservesOthers(tags[1..], tag, other);
    }
  }

  function ClampLap(lap: Lap): Lap
    ensures ClampLap(lap).timestamp >= 0
    ensures ClampLap(lap).duration >= 0
    ensures ClampLap(lap).expectedDuration >= -1
  {
    Lap(
      if lap.timestamp >= 0 then lap.timestamp else 0,
      if lap.duration >= 0 then lap.duration else 0,
      lap.section,
      lap.selected,
      if lap.expectedDuration >= -1 then lap.expectedDuration else -1,
      lap.tags
    )
  }

  // Convert a template entry back to a lap
  function TemplateEntryToLap(entry: TemplateEntry): Lap
    ensures TemplateEntryToLap(entry).timestamp >= 0
    ensures TemplateEntryToLap(entry).duration >= 0
    ensures TemplateEntryToLap(entry).expectedDuration == -1
  {
    Lap(
      0,  // timestamp
      if entry.expectedDuration >= 0 then entry.expectedDuration else 0,  // duration from expected
      entry.section,
      true,  // selected
      -1,    // no expected duration (it's not practice mode anymore)
      entry.tags
    )
  }

  // Convert all template entries to laps
  function TemplateToLaps(template: seq<TemplateEntry>): seq<Lap>
    ensures |TemplateToLaps(template)| == |template|
    ensures LapsValid(TemplateToLaps(template))
  {
    if |template| == 0 then []
    else [TemplateEntryToLap(template[0])] + TemplateToLaps(template[1..])
  }

  function ClampLaps(laps: seq<Lap>): seq<Lap>
    ensures |ClampLaps(laps)| == |laps|
    ensures forall i | 0 <= i < |laps| :: ClampLaps(laps)[i] == ClampLap(laps[i])
    ensures LapsValid(ClampLaps(laps))
  {
    if |laps| == 0 then []
    else [ClampLap(laps[0])] + ClampLaps(laps[1..])
  }

  //----------------------------------------------------------------------
  // Invariants
  //----------------------------------------------------------------------

  ghost predicate LapsValid(laps: seq<Lap>) {
    forall i | 0 <= i < |laps| ::
      laps[i].timestamp >= 0 && laps[i].duration >= 0 && laps[i].expectedDuration >= -1
  }

  ghost predicate Inv(m: Model) {
    m.currentTime >= 0 &&
    m.lastLapTime >= 0 &&
    m.lastLapTime <= m.currentTime &&
    LapsValid(m.laps) &&
    m.activeSection >= -1 &&
    (m.activeSection >= 0 ==> m.activeSection < |m.originalTemplate|)
  }

  //----------------------------------------------------------------------
  // State Machine Functions
  //----------------------------------------------------------------------

  function Init(): Model
    ensures Inv(Init())
  {
    Model(0, 0, [], [], [], -1)
  }

  function Apply(m: Model, a: Action): Model
  {
    match a
      case SetTime(ms) =>
        // Only allow time to advance forward
        if ms >= m.currentTime then Model(ms, m.lastLapTime, m.laps, m.template, m.originalTemplate, m.activeSection) else m

      case CreateLap =>
        // Record lap with duration from last lap time
        var duration := m.currentTime - m.lastLapTime;
        var newLap := Lap(m.currentTime, duration, "", false, -1, []);
        Model(m.currentTime, m.currentTime, m.laps + [newLap], m.template, m.originalTemplate, m.activeSection)

      case LabelLap(idx, name) =>
        if 0 <= idx < |m.laps| then
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(section := name)], m.template, m.originalTemplate, m.activeSection)
        else
          m

      case SelectLap(idx) =>
        if 0 <= idx < |m.laps| then
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(selected := !m.laps[idx].selected)], m.template, m.originalTemplate, m.activeSection)
        else
          m

      case DeleteLap(idx) =>
        // Delete lap - other laps keep their stored durations
        if 0 <= idx < |m.laps| then
          Model(m.currentTime, m.lastLapTime, m.laps[..idx] + m.laps[idx+1..], m.template, m.originalTemplate, m.activeSection)
        else
          m

      case AdjustDuration(idx, duration) =>
        // Manually set duration (must be non-negative)
        if 0 <= idx < |m.laps| && duration >= 0 then
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(duration := duration)], m.template, m.originalTemplate, m.activeSection)
        else
          m

      case MoveUp(idx) =>
        // Swap lap with the one above it
        if 1 <= idx < |m.laps| then
          var newLaps := m.laps[idx-1 := m.laps[idx]][idx := m.laps[idx-1]];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template, m.originalTemplate, m.activeSection)
        else
          m

      case MoveDown(idx) =>
        // Swap lap with the one below it
        if 0 <= idx < |m.laps| - 1 then
          var newLaps := m.laps[idx := m.laps[idx+1]][idx+1 := m.laps[idx]];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template, m.originalTemplate, m.activeSection)
        else
          m

      case AddTag(idx, tag) =>
        // Add tag to lap if not already present
        if 0 <= idx < |m.laps| then
          var newTags := AddTagToSeq(m.laps[idx].tags, tag);
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(tags := newTags)], m.template, m.originalTemplate, m.activeSection)
        else
          m

      case RemoveTag(idx, tag) =>
        // Remove tag from lap
        if 0 <= idx < |m.laps| then
          var newTags := RemoveTagFromSeq(m.laps[idx].tags, tag);
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(tags := newTags)], m.template, m.originalTemplate, m.activeSection)
        else
          m

      case SetTemplate(labels) =>
        // Set the practice template queue and store original for reset
        // Reset activeSection to -1 (start in sequential mode)
        Model(m.currentTime, m.lastLapTime, m.laps, labels, labels, -1)

      case ConsumeTemplate =>
        // Label last lap from template and select it, set expected duration and tags
        if |m.template| > 0 && |m.laps| > 0 then
          var idx := |m.laps| - 1;
          var entry := m.template[0];
          var expectedDur := if entry.expectedDuration >= 0 then entry.expectedDuration else -1;
          var newLaps := m.laps[idx := m.laps[idx].(section := entry.section, selected := true, expectedDuration := expectedDur, tags := entry.tags)];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template[1..], m.originalTemplate, m.activeSection)
        else
          m

      case SetActiveSection(idx) =>
        // Set active section for jump-to practice (-1 to clear and resume sequential)
        if idx >= -1 && (idx == -1 || idx < |m.originalTemplate|) then
          Model(m.currentTime, m.lastLapTime, m.laps, m.template, m.originalTemplate, idx)
        else
          m

      case ApplyActiveSection =>
        // Label last lap from active section (doesn't consume queue)
        if m.activeSection >= 0 && m.activeSection < |m.originalTemplate| && |m.laps| > 0 then
          var lapIdx := |m.laps| - 1;
          var entry := m.originalTemplate[m.activeSection];
          var expectedDur := if entry.expectedDuration >= 0 then entry.expectedDuration else -1;
          var newLaps := m.laps[lapIdx := m.laps[lapIdx].(section := entry.section, selected := true, expectedDuration := expectedDur, tags := entry.tags)];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template, m.originalTemplate, m.activeSection)
        else
          m

      case AdvanceTemplateAfter(idx) =>
        // Advance template queue to start after idx in originalTemplate
        // This allows continuing sequentially after a jump
        if idx >= 0 && idx < |m.originalTemplate| then
          var newTemplate := m.originalTemplate[idx + 1..];
          Model(m.currentTime, m.lastLapTime, m.laps, newTemplate, m.originalTemplate, -1)
        else
          m

      case ImportLaps(laps) =>
        // Import multiple laps at once (for paste import)
        // Clamp values to ensure validity
        var validLaps := ClampLaps(laps);
        Model(m.currentTime, m.lastLapTime, m.laps + validLaps, m.template, m.originalTemplate, m.activeSection)

      case Reset =>
        // If in practice mode, restore original template as laps; otherwise clear all
        // Reset activeSection to -1
        if |m.originalTemplate| > 0 then
          Model(m.currentTime, m.currentTime, TemplateToLaps(m.originalTemplate), [], [], -1)
        else
          Model(m.currentTime, m.currentTime, [], [], [], -1)
  }

  function Normalize(m: Model): Model {
    m
  }

  //----------------------------------------------------------------------
  // Core Lemmas
  //----------------------------------------------------------------------

  lemma InitSatisfiesInv()
    ensures Inv(Init())
  {}

  lemma StepPreservesInv(m: Model, a: Action)
    ensures Inv(Normalize(Apply(m, a)))
  {}

  //----------------------------------------------------------------------
  // Requirement Lemmas
  //----------------------------------------------------------------------

  // [verified] Timer elapsed time is always non-negative
  lemma ElapsedTimeNonNegative(m: Model)
    requires Inv(m)
    ensures m.currentTime >= 0
  {}

  // [verified] All lap durations are non-negative
  lemma LapDurationsNonNegative(m: Model)
    requires Inv(m)
    ensures forall i | 0 <= i < |m.laps| :: m.laps[i].duration >= 0
  {}

  // [verified] Deleting a lap preserves other laps' durations
  lemma DeletePreservesDurations(m: Model, idx: int)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures forall i | 0 <= i < idx ::
      Apply(m, DeleteLap(idx)).laps[i].duration == m.laps[i].duration
    ensures forall i | idx < i < |m.laps| ::
      Apply(m, DeleteLap(idx)).laps[i-1].duration == m.laps[i].duration
  {}

  // [verified] Adjusting duration only changes that lap
  lemma AdjustOnlyChangesDuration(m: Model, idx: int, dur: int)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    requires dur >= 0
    ensures Apply(m, AdjustDuration(idx, dur)).laps[idx].duration == dur
    ensures Apply(m, AdjustDuration(idx, dur)).laps[idx].section == m.laps[idx].section
    ensures Apply(m, AdjustDuration(idx, dur)).laps[idx].selected == m.laps[idx].selected
  {}

  // [verified] Selecting a lap toggles its selected state
  lemma SelectLapToggles(m: Model, idx: int)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures Apply(m, SelectLap(idx)).laps[idx].selected == !m.laps[idx].selected
  {}

  // [verified] Deleting a lap reduces the count by 1
  lemma DeleteLapReducesCount(m: Model, idx: int)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures |Apply(m, DeleteLap(idx)).laps| == |m.laps| - 1
  {}

  //----------------------------------------------------------------------
  // Lap Reordering Lemmas
  //----------------------------------------------------------------------

  // [verified] Moving a lap up swaps it with the previous lap
  lemma MoveUpSwaps(m: Model, idx: int)
    requires Inv(m)
    requires 1 <= idx < |m.laps|
    ensures Apply(m, MoveUp(idx)).laps[idx-1] == m.laps[idx]
    ensures Apply(m, MoveUp(idx)).laps[idx] == m.laps[idx-1]
  {}

  // [verified] Moving a lap down swaps it with the next lap
  lemma MoveDownSwaps(m: Model, idx: int)
    requires Inv(m)
    requires 0 <= idx < |m.laps| - 1
    ensures Apply(m, MoveDown(idx)).laps[idx] == m.laps[idx+1]
    ensures Apply(m, MoveDown(idx)).laps[idx+1] == m.laps[idx]
  {}

  // [verified] Moving the first lap up has no effect
  lemma MoveUpFirstNoEffect(m: Model)
    requires Inv(m)
    requires |m.laps| > 0
    ensures Apply(m, MoveUp(0)) == m
  {}

  // [verified] Moving the last lap down has no effect
  lemma MoveDownLastNoEffect(m: Model)
    requires Inv(m)
    requires |m.laps| > 0
    ensures Apply(m, MoveDown(|m.laps| - 1)) == m
  {}

  // [verified] Moving preserves lap count
  lemma MovePreservesCount(m: Model, idx: int)
    requires Inv(m)
    ensures |Apply(m, MoveUp(idx)).laps| == |m.laps|
    ensures |Apply(m, MoveDown(idx)).laps| == |m.laps|
  {}

  //----------------------------------------------------------------------
  // Tagging Lemmas
  //----------------------------------------------------------------------

  // [verified] Adding a tag preserves other lap data
  lemma AddTagPreservesLapData(m: Model, idx: int, tag: string)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures Apply(m, AddTag(idx, tag)).laps[idx].timestamp == m.laps[idx].timestamp
    ensures Apply(m, AddTag(idx, tag)).laps[idx].duration == m.laps[idx].duration
    ensures Apply(m, AddTag(idx, tag)).laps[idx].section == m.laps[idx].section
    ensures Apply(m, AddTag(idx, tag)).laps[idx].selected == m.laps[idx].selected
    ensures Apply(m, AddTag(idx, tag)).laps[idx].expectedDuration == m.laps[idx].expectedDuration
  {}

  // [verified] Removing a tag preserves other lap data
  lemma RemoveTagPreservesLapData(m: Model, idx: int, tag: string)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures Apply(m, RemoveTag(idx, tag)).laps[idx].timestamp == m.laps[idx].timestamp
    ensures Apply(m, RemoveTag(idx, tag)).laps[idx].duration == m.laps[idx].duration
    ensures Apply(m, RemoveTag(idx, tag)).laps[idx].section == m.laps[idx].section
    ensures Apply(m, RemoveTag(idx, tag)).laps[idx].selected == m.laps[idx].selected
    ensures Apply(m, RemoveTag(idx, tag)).laps[idx].expectedDuration == m.laps[idx].expectedDuration
  {}

  // [verified] Added tag is present in the lap's tags
  lemma AddTagAddsTag(m: Model, idx: int, tag: string)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures TagIn(tag, Apply(m, AddTag(idx, tag)).laps[idx].tags)
  {}

  // [verified] Removed tag is not present in the lap's tags
  lemma RemoveTagRemovesTag(m: Model, idx: int, tag: string)
    requires Inv(m)
    requires 0 <= idx < |m.laps|
    ensures !TagIn(tag, Apply(m, RemoveTag(idx, tag)).laps[idx].tags)
  {
    RemoveTagEnsuresAbsence(m.laps[idx].tags, tag);
  }

  //----------------------------------------------------------------------
  // Practice Mode Lemmas
  //----------------------------------------------------------------------

  // [verified] Consuming template sets the lap's section label
  lemma ConsumeTemplateSetsLabel(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures Apply(m, ConsumeTemplate).laps[|m.laps|-1].section == m.template[0].section
  {}

  // [verified] Consuming template sets the lap's expected duration
  lemma ConsumeTemplateSetsExpected(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    requires m.template[0].expectedDuration >= 0
    ensures Apply(m, ConsumeTemplate).laps[|m.laps|-1].expectedDuration == m.template[0].expectedDuration
  {}

  // [verified] Consuming template sets the lap's tags
  lemma ConsumeTemplateSetsTags(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures Apply(m, ConsumeTemplate).laps[|m.laps|-1].tags == m.template[0].tags
  {}

  // [verified] Consuming template selects the lap
  lemma ConsumeTemplateSelectsLap(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures Apply(m, ConsumeTemplate).laps[|m.laps|-1].selected == true
  {}

  // [verified] Template queue length decreases by one after consumption
  lemma ConsumeTemplateDecreasesQueue(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures |Apply(m, ConsumeTemplate).template| == |m.template| - 1
  {}

  //----------------------------------------------------------------------
  // Import Lemmas
  //----------------------------------------------------------------------

  // [verified] Importing laps preserves existing laps
  lemma ImportPreservesExisting(m: Model, laps: seq<Lap>)
    requires Inv(m)
    ensures forall i | 0 <= i < |m.laps| ::
      Apply(m, ImportLaps(laps)).laps[i] == m.laps[i]
  {}

  // [verified] Import appends laps to the end
  lemma ImportAppendsToEnd(m: Model, laps: seq<Lap>)
    requires Inv(m)
    ensures |Apply(m, ImportLaps(laps)).laps| == |m.laps| + |ClampLaps(laps)|
  {}

  //----------------------------------------------------------------------
  // Total Duration Helpers
  //----------------------------------------------------------------------

  function Sum(s: seq<int>): int
    ensures |s| == 0 ==> Sum(s) == 0
  {
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
  }

  lemma SumOfNonNegativeIsNonNegative(s: seq<int>)
    requires forall i | 0 <= i < |s| :: s[i] >= 0
    ensures Sum(s) >= 0
  {
    if |s| == 0 {
    } else {
      SumOfNonNegativeIsNonNegative(s[1..]);
    }
  }

  // [verified] Total duration of selected takes is non-negative
  lemma SelectedTotalIsNonNegative(durations: seq<int>)
    requires forall i | 0 <= i < |durations| :: durations[i] >= 0
    ensures Sum(durations) >= 0
  {
    SumOfNonNegativeIsNonNegative(durations);
  }

  //----------------------------------------------------------------------
  // Selected Total Helpers
  //----------------------------------------------------------------------

  // Extract durations of selected laps
  function SelectedDurations(laps: seq<Lap>): seq<int>
  {
    if |laps| == 0 then []
    else if laps[0].selected then [laps[0].duration] + SelectedDurations(laps[1..])
    else SelectedDurations(laps[1..])
  }

  // Compute total of selected laps
  function SelectedTotal(laps: seq<Lap>): int
  {
    Sum(SelectedDurations(laps))
  }

  // Count selected laps
  function SelectedCount(laps: seq<Lap>): int
  {
    |SelectedDurations(laps)|
  }

  // [verified] Selected count is non-negative
  lemma SelectedCountNonNegative(laps: seq<Lap>)
    ensures SelectedCount(laps) >= 0
  {}

  // [verified] Selected count equals number of selected laps
  lemma SelectedCountCorrect(laps: seq<Lap>)
    ensures SelectedCount(laps) == |SelectedDurations(laps)|
  {}

  // [verified] Selected total equals sum of selected lap durations
  lemma SelectedTotalCorrect(laps: seq<Lap>)
    ensures SelectedTotal(laps) == Sum(SelectedDurations(laps))
  {}

  // [verified] Selected total is non-negative when all durations are non-negative
  lemma SelectedTotalNonNegative(laps: seq<Lap>)
    requires LapsValid(laps)
    ensures SelectedTotal(laps) >= 0
  {
    SelectedDurationsNonNegative(laps);
    SumOfNonNegativeIsNonNegative(SelectedDurations(laps));
  }

  lemma SelectedDurationsNonNegative(laps: seq<Lap>)
    requires LapsValid(laps)
    ensures forall i | 0 <= i < |SelectedDurations(laps)| :: SelectedDurations(laps)[i] >= 0
  {
    if |laps| == 0 {
    } else {
      SelectedDurationsNonNegative(laps[1..]);
    }
  }

  //----------------------------------------------------------------------
  // Running Totals (prefix sums of selected lap durations)
  //----------------------------------------------------------------------

  // Helper: compute running totals with an accumulator
  function RunningTotalsHelper(laps: seq<Lap>, acc: int): seq<int>
    ensures |RunningTotalsHelper(laps, acc)| == |laps|
  {
    if |laps| == 0 then []
    else
      var newAcc := if laps[0].selected then acc + laps[0].duration else acc;
      [newAcc] + RunningTotalsHelper(laps[1..], newAcc)
  }

  // Compute running totals: RunningTotals(laps)[i] = sum of selected durations in laps[..i+1]
  function RunningTotals(laps: seq<Lap>): seq<int>
    ensures |RunningTotals(laps)| == |laps|
  {
    RunningTotalsHelper(laps, 0)
  }

  // [verified] Running totals length equals laps length
  lemma RunningTotalsLength(laps: seq<Lap>)
    ensures |RunningTotals(laps)| == |laps|
  {}

  // [verified] Last running total equals selected total
  lemma RunningTotalsFinalEqualsSelectedTotal(laps: seq<Lap>)
    requires |laps| > 0
    ensures RunningTotals(laps)[|laps| - 1] == SelectedTotal(laps)
  {
    RunningTotalsHelperFinalEqualsSelectedTotal(laps, 0);
  }

  // Helper lemma: final element of RunningTotalsHelper equals acc + SelectedTotal
  lemma RunningTotalsHelperFinalEqualsSelectedTotal(laps: seq<Lap>, acc: int)
    requires |laps| > 0
    ensures RunningTotalsHelper(laps, acc)[|laps| - 1] == acc + SelectedTotal(laps)
  {
    var newAcc := if laps[0].selected then acc + laps[0].duration else acc;
    if |laps| == 1 {
      assert laps[1..] == [];
      assert RunningTotalsHelper(laps, acc) == [newAcc];
      assert SelectedDurations(laps[1..]) == [];
    } else {
      RunningTotalsHelperFinalEqualsSelectedTotal(laps[1..], newAcc);
    }
  }

  // [verified] Running totals are non-negative when all durations are non-negative
  lemma RunningTotalsNonNegative(laps: seq<Lap>)
    requires LapsValid(laps)
    ensures forall i | 0 <= i < |RunningTotals(laps)| :: RunningTotals(laps)[i] >= 0
  {
    RunningTotalsHelperNonNegative(laps, 0);
  }

  lemma RunningTotalsHelperNonNegative(laps: seq<Lap>, acc: int)
    requires LapsValid(laps)
    requires acc >= 0
    ensures forall i | 0 <= i < |RunningTotalsHelper(laps, acc)| :: RunningTotalsHelper(laps, acc)[i] >= 0
  {
    if |laps| == 0 {
    } else {
      var newAcc := if laps[0].selected then acc + laps[0].duration else acc;
      RunningTotalsHelperNonNegative(laps[1..], newAcc);
    }
  }

  //----------------------------------------------------------------------
  // Tag Total Helpers
  //----------------------------------------------------------------------

  // Check if a lap has a specific tag
  predicate LapHasTag(lap: Lap, tag: string) {
    tag in lap.tags
  }

  // Sum durations of selected laps that have a specific tag
  function SumByTag(laps: seq<Lap>, tag: string): int
  {
    if |laps| == 0 then 0
    else if laps[0].selected && LapHasTag(laps[0], tag) then
      laps[0].duration + SumByTag(laps[1..], tag)
    else
      SumByTag(laps[1..], tag)
  }

  // [verified] SumByTag is non-negative when all durations are non-negative
  lemma SumByTagNonNegative(laps: seq<Lap>, tag: string)
    requires LapsValid(laps)
    ensures SumByTag(laps, tag) >= 0
  {
    if |laps| == 0 {
    } else {
      SumByTagNonNegative(laps[1..], tag);
    }
  }

  // [verified] SumByTag only counts selected laps
  lemma SumByTagOnlySelected(laps: seq<Lap>, tag: string)
    requires |laps| > 0
    requires !laps[0].selected
    ensures SumByTag(laps, tag) == SumByTag(laps[1..], tag)
  {}

  // [verified] SumByTag only counts laps with the tag
  lemma SumByTagOnlyTagged(laps: seq<Lap>, tag: string)
    requires |laps| > 0
    requires laps[0].selected
    requires !LapHasTag(laps[0], tag)
    ensures SumByTag(laps, tag) == SumByTag(laps[1..], tag)
  {}

  // Count selected laps that have a specific tag
  function CountByTag(laps: seq<Lap>, tag: string): int
  {
    if |laps| == 0 then 0
    else if laps[0].selected && LapHasTag(laps[0], tag) then
      1 + CountByTag(laps[1..], tag)
    else
      CountByTag(laps[1..], tag)
  }

  // [verified] CountByTag is non-negative
  lemma CountByTagNonNegative(laps: seq<Lap>, tag: string)
    ensures CountByTag(laps, tag) >= 0
  {
    if |laps| == 0 {
    } else {
      CountByTagNonNegative(laps[1..], tag);
    }
  }

  // Collect all unique tags from selected laps
  function CollectTagsFromLap(lap: Lap): seq<string>
  {
    if lap.selected then lap.tags else []
  }

  function CollectAllTagsHelper(laps: seq<Lap>, seen: seq<string>): seq<string>
  {
    if |laps| == 0 then seen
    else
      var newTags := CollectTagsFromLap(laps[0]);
      var updatedSeen := AddUniqueTags(seen, newTags);
      CollectAllTagsHelper(laps[1..], updatedSeen)
  }

  function AddUniqueTags(seen: seq<string>, tags: seq<string>): seq<string>
    decreases |tags|
  {
    if |tags| == 0 then seen
    else if tags[0] in seen then AddUniqueTags(seen, tags[1..])
    else AddUniqueTags(seen + [tags[0]], tags[1..])
  }

  function CollectAllTags(laps: seq<Lap>): seq<string>
  {
    CollectAllTagsHelper(laps, [])
  }

  // [verified] SumByTag includes duration when lap is selected and has tag
  lemma SumByTagIncludesDuration(laps: seq<Lap>, tag: string)
    requires |laps| > 0
    requires laps[0].selected
    requires LapHasTag(laps[0], tag)
    ensures SumByTag(laps, tag) == laps[0].duration + SumByTag(laps[1..], tag)
  {}

  //----------------------------------------------------------------------
  // Section Aggregation Helpers
  //----------------------------------------------------------------------

  // Sum durations of selected laps with a specific section
  function SumBySection(laps: seq<Lap>, section: string): int
  {
    if |laps| == 0 then 0
    else if laps[0].selected && laps[0].section == section then
      laps[0].duration + SumBySection(laps[1..], section)
    else
      SumBySection(laps[1..], section)
  }

  // Count selected laps with a specific section
  function CountBySection(laps: seq<Lap>, section: string): int
  {
    if |laps| == 0 then 0
    else if laps[0].selected && laps[0].section == section then
      1 + CountBySection(laps[1..], section)
    else
      CountBySection(laps[1..], section)
  }

  // Find minimum duration among selected laps with a specific section
  // Returns -1 if no matching laps
  function MinBySectionHelper(laps: seq<Lap>, section: string, currentMin: int): int
  {
    if |laps| == 0 then currentMin
    else if laps[0].selected && laps[0].section == section then
      var newMin := if currentMin == -1 then laps[0].duration
                    else if laps[0].duration < currentMin then laps[0].duration
                    else currentMin;
      MinBySectionHelper(laps[1..], section, newMin)
    else
      MinBySectionHelper(laps[1..], section, currentMin)
  }

  function MinBySection(laps: seq<Lap>, section: string): int
  {
    MinBySectionHelper(laps, section, -1)
  }

  // Find maximum duration among selected laps with a specific section
  // Returns -1 if no matching laps
  function MaxBySectionHelper(laps: seq<Lap>, section: string, currentMax: int): int
  {
    if |laps| == 0 then currentMax
    else if laps[0].selected && laps[0].section == section then
      var newMax := if laps[0].duration > currentMax then laps[0].duration
                    else currentMax;
      MaxBySectionHelper(laps[1..], section, newMax)
    else
      MaxBySectionHelper(laps[1..], section, currentMax)
  }

  function MaxBySection(laps: seq<Lap>, section: string): int
  {
    MaxBySectionHelper(laps, section, -1)
  }

  // Collect all unique sections from selected laps (non-empty sections only)
  function CollectAllSectionsHelper(laps: seq<Lap>, seen: seq<string>): seq<string>
  {
    if |laps| == 0 then seen
    else if laps[0].selected && laps[0].section != "" then
      var section := laps[0].section;
      var updatedSeen := if section in seen then seen else seen + [section];
      CollectAllSectionsHelper(laps[1..], updatedSeen)
    else
      CollectAllSectionsHelper(laps[1..], seen)
  }

  function CollectAllSections(laps: seq<Lap>): seq<string>
  {
    CollectAllSectionsHelper(laps, [])
  }

  // [verified] SumBySection is non-negative when all durations are non-negative
  lemma SumBySectionNonNegative(laps: seq<Lap>, section: string)
    requires LapsValid(laps)
    ensures SumBySection(laps, section) >= 0
  {
    if |laps| == 0 {
    } else {
      SumBySectionNonNegative(laps[1..], section);
    }
  }

  // [verified] CountBySection is non-negative
  lemma CountBySectionNonNegative(laps: seq<Lap>, section: string)
    ensures CountBySection(laps, section) >= 0
  {
    if |laps| == 0 {
    } else {
      CountBySectionNonNegative(laps[1..], section);
    }
  }

  // [verified] SumBySection only counts selected laps
  lemma SumBySectionOnlySelected(laps: seq<Lap>, section: string)
    requires |laps| > 0
    requires !laps[0].selected
    ensures SumBySection(laps, section) == SumBySection(laps[1..], section)
  {}

  // [verified] SumBySection only counts laps with the section
  lemma SumBySectionOnlyMatching(laps: seq<Lap>, section: string)
    requires |laps| > 0
    requires laps[0].selected
    requires laps[0].section != section
    ensures SumBySection(laps, section) == SumBySection(laps[1..], section)
  {}

  // Helper lemma for MinBySectionHelper
  lemma MinBySectionHelperValid(laps: seq<Lap>, section: string, currentMin: int)
    requires LapsValid(laps)
    requires currentMin >= -1
    ensures MinBySectionHelper(laps, section, currentMin) >= -1
  {
    if |laps| == 0 {
    } else if laps[0].selected && laps[0].section == section {
      var newMin := if currentMin == -1 then laps[0].duration
                    else if laps[0].duration < currentMin then laps[0].duration
                    else currentMin;
      MinBySectionHelperValid(laps[1..], section, newMin);
    } else {
      MinBySectionHelperValid(laps[1..], section, currentMin);
    }
  }

  // [verified] MinBySection returns -1 or a valid duration
  lemma MinBySectionValid(laps: seq<Lap>, section: string)
    requires LapsValid(laps)
    ensures MinBySection(laps, section) >= -1
  {
    MinBySectionHelperValid(laps, section, -1);
  }

  // Helper lemma for MaxBySectionHelper
  lemma MaxBySectionHelperValid(laps: seq<Lap>, section: string, currentMax: int)
    requires LapsValid(laps)
    requires currentMax >= -1
    ensures MaxBySectionHelper(laps, section, currentMax) >= -1
  {
    if |laps| == 0 {
    } else if laps[0].selected && laps[0].section == section {
      var newMax := if laps[0].duration > currentMax then laps[0].duration
                    else currentMax;
      MaxBySectionHelperValid(laps[1..], section, newMax);
    } else {
      MaxBySectionHelperValid(laps[1..], section, currentMax);
    }
  }

  // [verified] MaxBySection returns -1 or a valid duration
  lemma MaxBySectionValid(laps: seq<Lap>, section: string)
    requires LapsValid(laps)
    ensures MaxBySection(laps, section) >= -1
  {
    MaxBySectionHelperValid(laps, section, -1);
  }

  //----------------------------------------------------------------------
  // Active Section Lemmas
  //----------------------------------------------------------------------

  // [verified] SetActiveSection updates model state to selected index
  lemma SetActiveSectionUpdatesState(m: Model, idx: int)
    requires Inv(m)
    requires idx >= -1 && (idx == -1 || idx < |m.originalTemplate|)
    ensures Apply(m, SetActiveSection(idx)).activeSection == idx
  {}

  // [verified] ApplyActiveSection labels last lap from active section entry
  lemma ApplyActiveSectionSetsLabel(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    ensures Apply(m, ApplyActiveSection).laps[|m.laps|-1].section == m.originalTemplate[m.activeSection].section
  {}

  // [verified] ApplyActiveSection sets the lap to selected
  lemma ApplyActiveSectionSelectsLap(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    ensures Apply(m, ApplyActiveSection).laps[|m.laps|-1].selected == true
  {}

  // [verified] ApplyActiveSection sets expected duration from template
  lemma ApplyActiveSectionSetsExpected(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    requires m.originalTemplate[m.activeSection].expectedDuration >= 0
    ensures Apply(m, ApplyActiveSection).laps[|m.laps|-1].expectedDuration == m.originalTemplate[m.activeSection].expectedDuration
  {}

  // [verified] ApplyActiveSection sets tags from template
  lemma ApplyActiveSectionSetsTags(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    ensures Apply(m, ApplyActiveSection).laps[|m.laps|-1].tags == m.originalTemplate[m.activeSection].tags
  {}

  // [verified] ApplyActiveSection preserves original lap duration
  lemma ApplyActiveSectionPreservesDuration(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    ensures Apply(m, ApplyActiveSection).laps[|m.laps|-1].duration == m.laps[|m.laps|-1].duration
  {}

  // [verified] ApplyActiveSection preserves original lap timestamp
  lemma ApplyActiveSectionPreservesTimestamp(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    ensures Apply(m, ApplyActiveSection).laps[|m.laps|-1].timestamp == m.laps[|m.laps|-1].timestamp
  {}

  // [verified] ApplyActiveSection does not consume template queue
  lemma ApplyActiveSectionPreservesQueue(m: Model)
    requires Inv(m)
    requires m.activeSection >= 0 && m.activeSection < |m.originalTemplate|
    requires |m.laps| > 0
    ensures |Apply(m, ApplyActiveSection).template| == |m.template|
  {}

  //----------------------------------------------------------------------
  // Practice Round-Trip Lemmas
  //----------------------------------------------------------------------

  // [verified] ConsumeTemplate sets all fields from template entry
  lemma ConsumeTemplateRoundTrip(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures var result := Apply(m, ConsumeTemplate);
            var idx := |m.laps| - 1;
            var entry := m.template[0];
            result.laps[idx].section == entry.section &&
            result.laps[idx].selected == true &&
            result.laps[idx].tags == entry.tags &&
            (entry.expectedDuration >= 0 ==> result.laps[idx].expectedDuration == entry.expectedDuration)
  {}

  // [verified] ConsumeTemplate preserves original lap duration
  lemma ConsumeTemplatePreservesDuration(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures Apply(m, ConsumeTemplate).laps[|m.laps|-1].duration == m.laps[|m.laps|-1].duration
  {}

  // [verified] ConsumeTemplate preserves original lap timestamp
  lemma ConsumeTemplatePreservesTimestamp(m: Model)
    requires Inv(m)
    requires |m.template| > 0
    requires |m.laps| > 0
    ensures Apply(m, ConsumeTemplate).laps[|m.laps|-1].timestamp == m.laps[|m.laps|-1].timestamp
  {}

  //----------------------------------------------------------------------
  // Reset from Practice Mode Lemmas
  //----------------------------------------------------------------------

  // [verified] Reset in practice mode restores original template as laps
  lemma ResetRestoresOriginalTemplate(m: Model)
    requires Inv(m)
    requires |m.originalTemplate| > 0
    ensures |Apply(m, Reset).laps| == |m.originalTemplate|
    ensures Apply(m, Reset).laps == TemplateToLaps(m.originalTemplate)
  {}

  // [verified] Reset in practice mode clears template (exits practice mode)
  lemma ResetClearsTemplate(m: Model)
    requires Inv(m)
    requires |m.originalTemplate| > 0
    ensures |Apply(m, Reset).template| == 0
    ensures |Apply(m, Reset).originalTemplate| == 0
  {}

  // [verified] Reset in practice mode: each restored lap has correct section from original template
  lemma ResetRestoresCorrectSections(m: Model, i: int)
    requires Inv(m)
    requires |m.originalTemplate| > 0
    requires 0 <= i < |m.originalTemplate|
    ensures Apply(m, Reset).laps[i].section == m.originalTemplate[i].section
  {
    TemplateToLapsPreservesSection(m.originalTemplate, i);
  }

  // Helper: TemplateToLaps preserves section at each index
  lemma TemplateToLapsPreservesSection(template: seq<TemplateEntry>, i: int)
    requires 0 <= i < |template|
    ensures TemplateToLaps(template)[i].section == template[i].section
  {
    if i == 0 {
    } else {
      TemplateToLapsPreservesSection(template[1..], i - 1);
    }
  }

  // [verified] Reset in practice mode: each restored lap has correct tags from original template
  lemma ResetRestoresCorrectTags(m: Model, i: int)
    requires Inv(m)
    requires |m.originalTemplate| > 0
    requires 0 <= i < |m.originalTemplate|
    ensures Apply(m, Reset).laps[i].tags == m.originalTemplate[i].tags
  {
    TemplateToLapsPreservesTags(m.originalTemplate, i);
  }

  // Helper: TemplateToLaps preserves tags at each index
  lemma TemplateToLapsPreservesTags(template: seq<TemplateEntry>, i: int)
    requires 0 <= i < |template|
    ensures TemplateToLaps(template)[i].tags == template[i].tags
  {
    if i == 0 {
    } else {
      TemplateToLapsPreservesTags(template[1..], i - 1);
    }
  }
}

// AppCore: concrete Kernel instantiated with TalkTimer domain
module AppCore refines Kernel {
  import D = TalkTimer

  // Expose verified computation functions
  function SelectedTotal(laps: seq<D.Lap>): int {
    D.SelectedTotal(laps)
  }

  function SelectedCount(laps: seq<D.Lap>): int {
    D.SelectedCount(laps)
  }

  function SumByTag(laps: seq<D.Lap>, tag: string): int {
    D.SumByTag(laps, tag)
  }

  function CountByTag(laps: seq<D.Lap>, tag: string): int {
    D.CountByTag(laps, tag)
  }

  function CollectAllTags(laps: seq<D.Lap>): seq<string> {
    D.CollectAllTags(laps)
  }

  // Section aggregation functions
  function SumBySection(laps: seq<D.Lap>, section: string): int {
    D.SumBySection(laps, section)
  }

  function CountBySection(laps: seq<D.Lap>, section: string): int {
    D.CountBySection(laps, section)
  }

  function MinBySection(laps: seq<D.Lap>, section: string): int {
    D.MinBySection(laps, section)
  }

  function MaxBySection(laps: seq<D.Lap>, section: string): int {
    D.MaxBySection(laps, section)
  }

  function CollectAllSections(laps: seq<D.Lap>): seq<string> {
    D.CollectAllSections(laps)
  }

  function RunningTotals(laps: seq<D.Lap>): seq<int> {
    D.RunningTotals(laps)
  }
}
