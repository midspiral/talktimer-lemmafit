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
    expectedDuration: int  // expected duration from practice template (-1 = none)
  )

  // Template entry for practice mode
  datatype TemplateEntry = TemplateEntry(section: string, expectedDuration: int)

  // The timer state
  datatype Model = Model(
    currentTime: int,   // current elapsed ms
    lastLapTime: int,   // timestamp of previous lap (for computing next duration)
    laps: seq<Lap>,     // recorded lap markers
    template: seq<TemplateEntry>  // practice mode template queue
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
    | SetTemplate(labels: seq<TemplateEntry>)  // set practice template queue
    | ConsumeTemplate                       // label last lap from template, select it
    | Reset                                 // clear all laps

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
    LapsValid(m.laps)
  }

  //----------------------------------------------------------------------
  // State Machine Functions
  //----------------------------------------------------------------------

  function Init(): Model
    ensures Inv(Init())
  {
    Model(0, 0, [], [])
  }

  function Apply(m: Model, a: Action): Model
  {
    match a
      case SetTime(ms) =>
        // Only allow time to advance forward
        if ms >= m.currentTime then Model(ms, m.lastLapTime, m.laps, m.template) else m

      case CreateLap =>
        // Record lap with duration from last lap time
        var duration := m.currentTime - m.lastLapTime;
        var newLap := Lap(m.currentTime, duration, "", false, -1);
        Model(m.currentTime, m.currentTime, m.laps + [newLap], m.template)

      case LabelLap(idx, name) =>
        if 0 <= idx < |m.laps| then
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(section := name)], m.template)
        else
          m

      case SelectLap(idx) =>
        if 0 <= idx < |m.laps| then
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(selected := !m.laps[idx].selected)], m.template)
        else
          m

      case DeleteLap(idx) =>
        // Delete lap - other laps keep their stored durations
        if 0 <= idx < |m.laps| then
          Model(m.currentTime, m.lastLapTime, m.laps[..idx] + m.laps[idx+1..], m.template)
        else
          m

      case AdjustDuration(idx, duration) =>
        // Manually set duration (must be non-negative)
        if 0 <= idx < |m.laps| && duration >= 0 then
          Model(m.currentTime, m.lastLapTime,
                m.laps[idx := m.laps[idx].(duration := duration)], m.template)
        else
          m

      case MoveUp(idx) =>
        // Swap lap with the one above it
        if 1 <= idx < |m.laps| then
          var newLaps := m.laps[idx-1 := m.laps[idx]][idx := m.laps[idx-1]];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template)
        else
          m

      case MoveDown(idx) =>
        // Swap lap with the one below it
        if 0 <= idx < |m.laps| - 1 then
          var newLaps := m.laps[idx := m.laps[idx+1]][idx+1 := m.laps[idx]];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template)
        else
          m

      case SetTemplate(labels) =>
        // Set the practice template queue
        Model(m.currentTime, m.lastLapTime, m.laps, labels)

      case ConsumeTemplate =>
        // Label last lap from template and select it, set expected duration
        if |m.template| > 0 && |m.laps| > 0 then
          var idx := |m.laps| - 1;
          var entry := m.template[0];
          var expectedDur := if entry.expectedDuration >= 0 then entry.expectedDuration else -1;
          var newLaps := m.laps[idx := m.laps[idx].(section := entry.section, selected := true, expectedDuration := expectedDur)];
          Model(m.currentTime, m.lastLapTime, newLaps, m.template[1..])
        else
          m

      case Reset =>
        // Clear all laps, reset lastLapTime to current time, clear template
        Model(m.currentTime, m.currentTime, [], [])
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
}

// AppCore: concrete Kernel instantiated with TalkTimer domain
module AppCore refines Kernel {
  import D = TalkTimer
}
