# Talk Timer Specification

A talk rehearsal timer that tracks lap times, organizes takes by section, and computes optimal talk duration.

## Feature: Timer Core Logic

- [verified] Timer displays elapsed time in minutes and seconds format (MM:SS)
- [verified] A single tap or keypress creates a lap marker at the current elapsed time
- [verified] Each lap records the duration from the previous lap marker (or start) to the current marker

## Feature: Session Data Model

- [verified] Sessions are organized hierarchically: a Talk contains Sections, each Section contains one or more Takes
- [verified] Each lap can be labeled with a section name after it is recorded
- [verified] All takes are preserved with their timestamps and durations

## Feature: Take Selection & Assembly

- [verified] Users can manually select which takes to include in the final talk total
- [verified] Users can delete unwanted or noisy takes (without affecting other takes' durations)
- [verified] Users can manually adjust the duration of any take
- [verified] Total estimated talk duration is computed by summing the selected takes
- [verified] Selected total equals sum of selected lap durations
- [verified] Selected total is non-negative when all durations are non-negative

## Feature: Lap Reordering

- [verified] Moving a lap up swaps it with the previous lap
- [verified] Moving a lap down swaps it with the next lap
- [verified] Moving preserves all lap data (duration, label, selection, expected)
- [verified] Moving the first lap up has no effect
- [verified] Moving the last lap down has no effect

## Feature: Practice Mode

- [verified] Starting practice captures section labels as a template queue
- [verified] Each lap in practice mode consumes one template entry
- [verified] Consumed template entry sets the lap's section label
- [verified] Consumed template entry sets the lap's expected duration
- [verified] Consumed template entry sets the lap's tags
- [verified] Template queue length decreases by one after consumption
- [verified] Consuming template sets all fields (section, selected, tags, expected) from entry
- [verified] Consuming template preserves original lap duration
- [verified] Consuming template preserves original lap timestamp
- [verified] Reset in practice mode restores ORIGINAL template as laps (not remaining)
- [verified] Reset in practice mode clears both template and originalTemplate (exits practice mode)
- [verified] Reset in practice mode: each restored lap has correct section from original template
- [verified] Reset in practice mode: each restored lap has correct tags from original template

## Feature: Import/Export

- [verified] Importing laps preserves existing laps
- [verified] Imported laps are appended to the end of the lap list
- [verified] Import is atomic (single undo removes all imported laps)

## Feature: Undo/Redo System

- [verified] All lap, label, select, and delete actions support undo and redo operations
- [verified] The undo/redo stack preserves complete action history for the session

## Feature: User Interface

- [trusted] The app provides a translucent overlay mode that stays visible but unobtrusive during rehearsal
- [trusted] Visual design uses soft muted colors for minimal distraction
- [trusted] A soft visual indicator shows progress toward a target talk duration when set
- [trusted] Sessions can be exported as Markdown summaries

## Feature: Tagging

- [verified] Each lap can have zero or more tags
- [verified] Adding a tag to a lap makes it present in the lap's tags
- [verified] Removing a tag from a lap makes it absent from the lap's tags
- [verified] Adding a tag to a lap preserves other lap data
- [verified] Removing a tag from a lap preserves other lap data
- [trusted] Tags are displayed as chips on each lap
- [trusted] Users can add tags via a + button
- [verified] SumByTag is non-negative when all durations are non-negative
- [verified] SumByTag only counts selected laps
- [verified] SumByTag only counts laps with the specified tag
- [verified] SumByTag includes duration when lap is selected and has tag
- [trusted] Total time by tag is displayed for selected laps
- [trusted] Tags are included in Markdown export
- [trusted] Tags are parsed from Markdown import

## Feature: Jump to Section Practice Mode

- [verified] Setting active section updates model state to selected index
- [verified] Active section index must be -1 (sequential) or valid index into originalTemplate
- [verified] ApplyActiveSection labels last lap from active section entry
- [verified] ApplyActiveSection sets the lap to selected
- [verified] ApplyActiveSection sets expected duration from template
- [verified] ApplyActiveSection sets tags from template
- [verified] ApplyActiveSection preserves original lap duration
- [verified] ApplyActiveSection preserves original lap timestamp
- [verified] ApplyActiveSection does not consume template queue
- [trusted] User can click any section in template to set it as active
- [trusted] Active section is visually highlighted in section picker
- [trusted] "Sequential" option returns to default queue-based mode

## Feature: Section Statistics

- [verified] SumBySection is non-negative when all durations are non-negative
- [verified] SumBySection only counts selected laps
- [verified] SumBySection only counts laps with the specified section
- [verified] CountBySection is non-negative
- [verified] MinBySection returns -1 (no data) or a valid duration
- [verified] MaxBySection returns -1 (no data) or a valid duration
- [trusted] Section statistics panel shows count, total, average, best, worst per section
- [trusted] Section statistics only include selected laps
- [trusted] Best/worst only shown when multiple takes exist for a section

## Feature: Keyboard & Accessibility

- [trusted] All primary functions are accessible via keyboard shortcuts for hands-free operation
- [trusted] The app can be quickly shown and hidden during rehearsal
